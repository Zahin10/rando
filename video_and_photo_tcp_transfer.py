/*
 * ============================================================
 *  ESP32-S3 Freenove WROOM — Video Recorder + Photo on Demand
 *  FreeRTOS dual-core architecture:
 *  Core 0 — Photo command listener (always on)
 *  Core 1 — Recording + upload loop
 *
 * LED colors:
 * Orange  (255, 150,   0) — booting
 * White   (255, 255, 255) — connecting to WiFi
 * Blue    (  0,   0, 255) — camera warming up
 * Red     (255,   0,   0) — recording video
 * Orange  (255, 165,   0) — finalizing AVI
 * Green   (  0, 255,   0) — uploading to PC
 * Cyan    (  0, 200, 255) — waiting for keep/delete or taking photo
 * Yellow  (255, 255,   0) — paused
 * ============================================================
 */
#include "USB.h"
#include "esp_camera.h"
#include "Adafruit_NeoPixel.h"
#include "driver/sdmmc_host.h"
#include "sdmmc_cmd.h"
#include "esp_vfs_fat.h"
#include <WiFi.h>
#include <stdio.h>
#include <dirent.h>
#include "lwip/sockets.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/semphr.h"

const char* ssid     = "ATT5XBY34a";
const char* password = R"(!!!786tsf2kwk6sd687@@@!!!@@@%%%%)";

const char*    computerIP     = "192.168.1.216";
const uint16_t TRANSFER_PORT  = 5010;
const uint16_t CMD_PORT       = 5005;
const uint16_t PHOTO_CMD_PORT = 5006;
const uint16_t PHOTO_PORT     = 5011;

#define RECORD_SECONDS        35
#define JPEG_QUALITY          10
#define MAX_CONSECUTIVE_FAILS 10
#define VIDEO_PATH            "/sdcard/HVGA.avi"
#define AVI_HEADER_SIZE       252

static const uint32_t VID_W = 480;
static const uint32_t VID_H = 320;

#define LED_PIN   48
#define LED_COUNT  1
Adafruit_NeoPixel led(LED_COUNT, LED_PIN, NEO_GRB + NEO_KHZ800);

// ── Shared state ──────────────────────────────────────────────────────────────
volatile bool g_take_photo  = false;
volatile bool g_camera_busy = false;
volatile bool g_paused      = false;   // pause flag
SemaphoreHandle_t g_camera_mutex;

#define PWDN_GPIO_NUM   -1
#define RESET_GPIO_NUM  -1
#define XCLK_GPIO_NUM   15
#define SIOD_GPIO_NUM    4
#define SIOC_GPIO_NUM    5
#define Y9_GPIO_NUM     16
#define Y8_GPIO_NUM     17
#define Y7_GPIO_NUM     18
#define Y6_GPIO_NUM     12
#define Y5_GPIO_NUM     10
#define Y4_GPIO_NUM      8
#define Y3_GPIO_NUM      9
#define Y2_GPIO_NUM     11
#define VSYNC_GPIO_NUM   6
#define HREF_GPIO_NUM    7
#define PCLK_GPIO_NUM   13

static sdmmc_card_t* card = NULL;
WiFiServer cmdServer(CMD_PORT);
WiFiServer photoCmdServer(PHOTO_CMD_PORT);
WiFiServer pauseCmdServer(5007);

// ── LED ───────────────────────────────────────────────────────────────────────
void setLED(uint8_t r, uint8_t g, uint8_t b) {
    led.setPixelColor(0, led.Color(r, g, b));
    led.show();
}

// ── AVI helpers ───────────────────────────────────────────────────────────────
void writeU32(uint8_t* buf, int offset, uint32_t val) {
    buf[offset]   =  val        & 0xFF;
    buf[offset+1] = (val >>  8) & 0xFF;
    buf[offset+2] = (val >> 16) & 0xFF;
    buf[offset+3] = (val >> 24) & 0xFF;
}

void buildAviHeader(uint8_t* h, uint32_t fps, uint32_t numFrames, uint32_t dataSize) {
    memset(h, 0, AVI_HEADER_SIZE);
    memcpy(h,      "RIFF", 4);
    writeU32(h,  4, AVI_HEADER_SIZE - 8 + dataSize);
    memcpy(h+ 8,   "AVI ", 4);
    memcpy(h+12,   "LIST", 4);
    writeU32(h, 16, 192);
    memcpy(h+20,   "hdrl", 4);
    memcpy(h+24,   "avih", 4);
    writeU32(h, 28, 56);
    writeU32(h, 32, (fps > 0) ? 1000000 / fps : 33333);
    writeU32(h, 36, 0);
    writeU32(h, 40, 0x10);
    writeU32(h, 44, numFrames);
    writeU32(h, 48, 0);
    writeU32(h, 52, 1);
    writeU32(h, 56, 0);
    writeU32(h, 60, VID_W);
    writeU32(h, 64, VID_H);
    memcpy(h+88,   "LIST", 4);
    writeU32(h, 92, 124);
    memcpy(h+96,   "strl", 4);
    memcpy(h+100,  "strh", 4);
    writeU32(h, 104, 56);
    memcpy(h+108,  "vids", 4);
    memcpy(h+112,  "MJPG", 4);
    writeU32(h, 116, 0);
    writeU32(h, 120, 0);
    writeU32(h, 124, 0);
    writeU32(h, 128, 1);
    writeU32(h, 132, fps);
    writeU32(h, 136, 0);
    writeU32(h, 140, numFrames);
    writeU32(h, 144, 0);
    writeU32(h, 148, (uint32_t)-1);
    writeU32(h, 152, 0);
    writeU32(h, 156, VID_W);
    writeU32(h, 160, VID_H);
    memcpy(h+164,  "strf", 4);
    writeU32(h, 168, 40);
    writeU32(h, 172, 40);
    writeU32(h, 176, VID_W);
    writeU32(h, 180, VID_H);
    h[184] = 1;
    h[186] = 24;
    memcpy(h+188,  "MJPG", 4);
    writeU32(h, 192, VID_W * VID_H * 3);
    memcpy(h+212,  "LIST", 4);
    writeU32(h, 216, dataSize + 4);
    memcpy(h+220,  "movi", 4);
}

// ── Camera init ───────────────────────────────────────────────────────────────
bool initCameraVideo() {
    esp_camera_deinit();
    delay(100);
    camera_config_t cfg;
    cfg.ledc_channel  = LEDC_CHANNEL_0;
    cfg.ledc_timer    = LEDC_TIMER_0;
    cfg.pin_d0        = Y2_GPIO_NUM;
    cfg.pin_d1        = Y3_GPIO_NUM;
    cfg.pin_d2        = Y4_GPIO_NUM;
    cfg.pin_d3        = Y5_GPIO_NUM;
    cfg.pin_d4        = Y6_GPIO_NUM;
    cfg.pin_d5        = Y7_GPIO_NUM;
    cfg.pin_d6        = Y8_GPIO_NUM;
    cfg.pin_d7        = Y9_GPIO_NUM;
    cfg.pin_xclk      = XCLK_GPIO_NUM;
    cfg.pin_pclk      = PCLK_GPIO_NUM;
    cfg.pin_vsync     = VSYNC_GPIO_NUM;
    cfg.pin_href      = HREF_GPIO_NUM;
    cfg.pin_sccb_sda  = SIOD_GPIO_NUM;
    cfg.pin_sccb_scl  = SIOC_GPIO_NUM;
    cfg.pin_pwdn      = PWDN_GPIO_NUM;
    cfg.pin_reset     = RESET_GPIO_NUM;
    cfg.xclk_freq_hz  = 20000000;
    cfg.pixel_format  = PIXFORMAT_JPEG;
    cfg.frame_size    = FRAMESIZE_HVGA;
    cfg.jpeg_quality  = JPEG_QUALITY;
    cfg.fb_count      = 2;
    cfg.fb_location   = CAMERA_FB_IN_PSRAM;
    cfg.grab_mode     = CAMERA_GRAB_LATEST;
    if (esp_camera_init(&cfg) != ESP_OK) return false;
    sensor_t* s = esp_camera_sensor_get();
    if (s) {
        s->set_vflip(s, 1);
        s->set_hmirror(s, 0);
        s->set_exposure_ctrl(s, 1);
        s->set_aec2(s, 1);
        s->set_ae_level(s, 0);
        s->set_gainceiling(s, (gainceiling_t)4);
        s->set_agc_gain(s, 0);
        s->set_whitebal(s, 1);
        s->set_awb_gain(s, 1);
        s->set_wb_mode(s, 0);
        s->set_brightness(s, 0);
        s->set_contrast(s, 2);
        s->set_saturation(s, 1);
        s->set_sharpness(s, 2);
        s->set_denoise(s, 1);
        s->set_special_effect(s, 0);
        s->set_lenc(s, 1);
        s->set_bpc(s, 1);
        s->set_wpc(s, 1);
        s->set_raw_gma(s, 1);
    }
    return true;
}

bool initCameraPhoto() {
    esp_camera_deinit();
    delay(100);
    camera_config_t cfg;
    cfg.ledc_channel  = LEDC_CHANNEL_0;
    cfg.ledc_timer    = LEDC_TIMER_0;
    cfg.pin_d0        = Y2_GPIO_NUM;
    cfg.pin_d1        = Y3_GPIO_NUM;
    cfg.pin_d2        = Y4_GPIO_NUM;
    cfg.pin_d3        = Y5_GPIO_NUM;
    cfg.pin_d4        = Y6_GPIO_NUM;
    cfg.pin_d5        = Y7_GPIO_NUM;
    cfg.pin_d6        = Y8_GPIO_NUM;
    cfg.pin_d7        = Y9_GPIO_NUM;
    cfg.pin_xclk      = XCLK_GPIO_NUM;
    cfg.pin_pclk      = PCLK_GPIO_NUM;
    cfg.pin_vsync     = VSYNC_GPIO_NUM;
    cfg.pin_href      = HREF_GPIO_NUM;
    cfg.pin_sccb_sda  = SIOD_GPIO_NUM;
    cfg.pin_sccb_scl  = SIOC_GPIO_NUM;
    cfg.pin_pwdn      = PWDN_GPIO_NUM;
    cfg.pin_reset     = RESET_GPIO_NUM;
    cfg.xclk_freq_hz  = 20000000;
    cfg.pixel_format  = PIXFORMAT_JPEG;
    cfg.frame_size    = FRAMESIZE_QXGA;
    cfg.jpeg_quality  = 8;
    cfg.fb_count      = 1;
    cfg.fb_location   = CAMERA_FB_IN_PSRAM;
    cfg.grab_mode     = CAMERA_GRAB_LATEST;
    if (esp_camera_init(&cfg) != ESP_OK) return false;
    sensor_t* s = esp_camera_sensor_get();
    if (s) {
        s->set_vflip(s, 1);
        s->set_hmirror(s, 0);
        s->set_brightness(s, 1);
        s->set_saturation(s, -2);
        s->set_sharpness(s, 2);
        s->set_contrast(s, 1);
        s->set_whitebal(s, 1);
        s->set_awb_gain(s, 1);
        s->set_wb_mode(s, 0);
        s->set_gain_ctrl(s, 1);
        s->set_exposure_ctrl(s, 1);
        s->set_aec2(s, 1);
        s->set_ae_level(s, 1);
        s->set_gainceiling(s, (gainceiling_t)6);
        s->set_denoise(s, 0);
        s->set_special_effect(s, 0);
        s->set_lenc(s, 1);
        s->set_bpc(s, 1);
        s->set_wpc(s, 1);
        s->set_raw_gma(s, 1);
    }
    return true;
}

// ── TCP helpers ───────────────────────────────────────────────────────────────
bool sendPhoto(uint8_t* buf, size_t len) {
    struct sockaddr_in dest;
    memset(&dest, 0, sizeof(dest));
    dest.sin_family = AF_INET;
    dest.sin_port   = htons(PHOTO_PORT);
    inet_aton(computerIP, &dest.sin_addr);
    int sock = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (sock < 0) return false;
    int sndbuf = 65536;
    setsockopt(sock, SOL_SOCKET, SO_SNDBUF, &sndbuf, sizeof(sndbuf));
    int flag = 1;
    setsockopt(sock, IPPROTO_TCP, TCP_NODELAY, &flag, sizeof(flag));
    if (connect(sock, (struct sockaddr*)&dest, sizeof(dest)) != 0) {
        close(sock); return false;
    }
    char header[64];
    int hlen = snprintf(header, sizeof(header), "photo.jpg:%d\n", (int)len);
    send(sock, header, hlen, 0);
    size_t sent = 0;
    while (sent < len) {
        int ret = send(sock, buf + sent, len - sent, 0);
        if (ret < 0) { close(sock); return false; }
        sent += ret;
    }
    close(sock);
    return true;
}

bool uploadFile(const char* sdPath) {
    struct sockaddr_in dest;
    memset(&dest, 0, sizeof(dest));
    dest.sin_family = AF_INET;
    dest.sin_port   = htons(TRANSFER_PORT);
    inet_aton(computerIP, &dest.sin_addr);
    int sock = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (sock < 0) return false;
    int sndbuf = 65536;
    setsockopt(sock, SOL_SOCKET, SO_SNDBUF, &sndbuf, sizeof(sndbuf));
    int flag = 1;
    setsockopt(sock, IPPROTO_TCP, TCP_NODELAY, &flag, sizeof(flag));
    if (connect(sock, (struct sockaddr*)&dest, sizeof(dest)) != 0) {
        close(sock); return false;
    }
    const char* filename = strrchr(sdPath, '/');
    filename = filename ? filename + 1 : sdPath;
    FILE* f = fopen(sdPath, "rb");
    if (!f) { close(sock); return false; }
    fseek(f, 0, SEEK_END);
    long fileSize = ftell(f);
    fseek(f, 0, SEEK_SET);
    char header[128];
    int hlen = snprintf(header, sizeof(header), "%s:%ld\n", filename, fileSize);
    send(sock, header, hlen, 0);
    const size_t BUF_SIZE = 32 * 1024;
    uint8_t* buf = (uint8_t*)malloc(BUF_SIZE);
    size_t bytesSent = 0;
    size_t bytesRead;
    while ((bytesRead = fread(buf, 1, BUF_SIZE, f)) > 0) {
        size_t sent = 0;
        while (sent < bytesRead) {
            int ret = send(sock, buf + sent, bytesRead - sent, 0);
            if (ret < 0) goto cleanup;
            sent += ret;
        }
        bytesSent += bytesRead;
    }
cleanup:
    free(buf);
    fclose(f);
    close(sock);
    return (bytesSent == (size_t)fileSize);
}

// ── Wait for keep/delete/pause/resume command ─────────────────────────────────
String waitForCommand() {
    long timeout = millis() + 300000;
    while (millis() < timeout) {
        if (g_take_photo) {
            Serial.println("[CMD] Photo requested — skipping keep/delete wait");
            return "keep";
        }
        WiFiClient client = cmdServer.available();
        if (client) {
            String cmd = "";
            long cmdTimeout = millis() + 5000;
            while (client.connected() && millis() < cmdTimeout) {
                if (client.available()) {
                    char c = client.read();
                    if (c == '\n') break;
                    cmd += c;
                }
            }
            cmd.trim();
            client.stop();
            // Handle pause/resume inline — don't return, keep waiting
            if (cmd == "pause") {
                g_paused = true;
                setLED(255, 255, 0);
                Serial.println("[CMD] Paused (in waitForCommand)");
                continue;
            }
            if (cmd == "resume") {
                g_paused = false;
                setLED(0, 200, 255);
                Serial.println("[CMD] Resumed (in waitForCommand)");
                continue;
            }
            return cmd;
        }
        delay(100);
    }
    return "keep";
}

void formatSD() {
    DIR* dir = opendir("/sdcard");
    if (dir) {
        struct dirent* entry;
        while ((entry = readdir(dir)) != NULL) {
            char path[300];
            snprintf(path, sizeof(path), "/sdcard/%s", entry->d_name);
            remove(path);
        }
        closedir(dir);
    }
    Serial.println("[SD] Formatted");
}

// ── Photo capture ─────────────────────────────────────────────────────────────
bool doPhotoCapture() {
    Serial.println("[PHOTO] Taking photo...");
    setLED(0, 200, 255);

    xSemaphoreTake(g_camera_mutex, portMAX_DELAY);

    if (!initCameraPhoto()) {
        Serial.println("[PHOTO] Camera init failed");
        initCameraVideo();
        xSemaphoreGive(g_camera_mutex);
        return false;
    }

    for (int i = 0; i < 30; i++) {
        camera_fb_t* fb = esp_camera_fb_get();
        if (fb) esp_camera_fb_return(fb);
        delay(100);
    }

    camera_fb_t* fb = esp_camera_fb_get();
    bool photoOk = false;
    if (!fb) {
        Serial.println("[PHOTO] Capture failed");
    } else {
        Serial.printf("[PHOTO] Captured %d bytes — sending...\n", fb->len);
        photoOk = sendPhoto(fb->buf, fb->len);
        esp_camera_fb_return(fb);
        Serial.println(photoOk ? "[PHOTO] Sent OK" : "[PHOTO] Send failed");
    }

    initCameraVideo();
    for (int i = 0; i < 10; i++) {
        camera_fb_t* fb = esp_camera_fb_get();
        if (fb) esp_camera_fb_return(fb);
        delay(50);
    }

    xSemaphoreGive(g_camera_mutex);
    setLED(255, 0, 0);
    Serial.println("[PHOTO] Back to video mode.");
    return photoOk;
}

// ── Core 0 — Photo listener task ─────────────────────────────────────────────
void photoListenerTask(void* pvParameters) {
    Serial.printf("[PHOTO TASK] Listening on port %d (Core %d)\n",
                  PHOTO_CMD_PORT, xPortGetCoreID());
    while (true) {
        WiFiClient client = photoCmdServer.available();
        if (client) {
            String cmd = "";
            long timeout = millis() + 5000;
            while (millis() < timeout) {
                while (client.available()) {
                    char c = client.read();
                    if (c == '\n') goto done;
                    cmd += c;
                }
                vTaskDelay(pdMS_TO_TICKS(10));
            }
            done:
            cmd.trim();
            client.stop();
            Serial.printf("[PHOTO TASK] Received: %s\n", cmd.c_str());
            if (cmd == "take_photo") {
                g_take_photo = true;
                Serial.println("[PHOTO TASK] Photo flag set!");
            }
        }
        vTaskDelay(pdMS_TO_TICKS(50));
    }
}

// ── Core 1 — Recording task ───────────────────────────────────────────────────
void recordingTask(void* pvParameters) {
    Serial.printf("[REC TASK] Starting on Core %d\n", xPortGetCoreID());

    setLED(0, 0, 255);
    int warmupFails = 0;
    for (int i = 0; i < 20; i++) {
        camera_fb_t* fb = esp_camera_fb_get();
        if (fb) { esp_camera_fb_return(fb); }
        else    { warmupFails++; }
        vTaskDelay(pdMS_TO_TICKS(100));
    }
    if (warmupFails > 10) {
        Serial.println("[REC TASK] Warmup failed — halting");
        setLED(255, 0, 0);
        while (true) vTaskDelay(pdMS_TO_TICKS(1000));
    }
    Serial.println("[REC TASK] Camera warmed up OK");

    cmdServer.begin();

    while (true) {

        // Handle pause between clips — wait here until resumed
        while (g_paused && !g_take_photo) {
            setLED(255, 255, 0);
            Serial.println("[REC TASK] Paused between clips — waiting...");
            vTaskDelay(pdMS_TO_TICKS(500));

            // Still need to check for commands while paused
            WiFiClient client = cmdServer.available();
            if (client) {
                String cmd = "";
                long cmdTimeout = millis() + 5000;
                while (client.connected() && millis() < cmdTimeout) {
                    if (client.available()) {
                        char c = client.read();
                        if (c == '\n') break;
                        cmd += c;
                    }
                }
                cmd.trim();
                client.stop();
                if (cmd == "resume") {
                    g_paused = false;
                    Serial.println("[REC TASK] Resumed between clips");
                }
            }
        }

        // Photo requested between clips
        if (g_take_photo) {
            g_take_photo = false;
            doPhotoCapture();
            continue;
        }

        // ── Start new clip ────────────────────────────────────────────────────
        remove(VIDEO_PATH);
        FILE* aviFile = fopen(VIDEO_PATH, "wb");
        if (!aviFile) {
            Serial.println("[REC TASK] Cannot open file");
            vTaskDelay(pdMS_TO_TICKS(1000));
            continue;
        }

        uint8_t placeholder[AVI_HEADER_SIZE];
        memset(placeholder, 0, AVI_HEADER_SIZE);
        fwrite(placeholder, 1, AVI_HEADER_SIZE, aviFile);

        Serial.printf("\n[REC TASK] Recording for %d seconds...\n", RECORD_SECONDS);
        setLED(255, 0, 0);

        uint32_t frameCount       = 0;
        uint32_t droppedFrames    = 0;
        uint32_t dataSize         = 0;
        uint32_t consecutiveFails = 0;
        uint32_t startTime        = millis();
        uint32_t pausedMs         = 0;     // total time spent paused
        bool     photoInterrupted = false;

        // ── Frame capture loop ────────────────────────────────────────────────
        while ((millis() - startTime - pausedMs) < (uint32_t)(RECORD_SECONDS * 1000UL)) {

            if (g_take_photo) {
                Serial.println("[REC TASK] Photo requested — finishing clip early");
                photoInterrupted = true;
                break;
            }

            // ── Pause handling inside recording loop ──────────────────────────
            if (g_paused) {
                setLED(255, 255, 0);
                Serial.println("[REC TASK] Paused mid-recording...");
                uint32_t pauseStart = millis();
                while (g_paused && !g_take_photo) {
                    vTaskDelay(pdMS_TO_TICKS(200));
                    // Check for resume command
                    WiFiClient client = cmdServer.available();
                    if (client) {
                        String cmd = "";
                        long cmdTimeout = millis() + 5000;
                        while (client.connected() && millis() < cmdTimeout) {
                            if (client.available()) {
                                char c = client.read();
                                if (c == '\n') break;
                                cmd += c;
                            }
                        }
                        cmd.trim();
                        client.stop();
                        if (cmd == "resume") {
                            g_paused = false;
                            Serial.println("[REC TASK] Resumed mid-recording");
                        }
                        if (cmd == "take_photo") {
                            g_take_photo = true;
                        }
                    }
                }
                pausedMs += (millis() - pauseStart);
                setLED(255, 0, 0);
                continue;
            }

            xSemaphoreTake(g_camera_mutex, portMAX_DELAY);
            camera_fb_t* fb = esp_camera_fb_get();
            xSemaphoreGive(g_camera_mutex);

            if (!fb) {
                consecutiveFails++;
                droppedFrames++;
                if (consecutiveFails >= MAX_CONSECUTIVE_FAILS) {
                    Serial.println("[REC TASK] Too many consecutive failures");
                    break;
                }
                vTaskDelay(pdMS_TO_TICKS(10));
                continue;
            }
            consecutiveFails = 0;

            uint8_t chunkHdr[8];
            memcpy(chunkHdr, "00dc", 4);
            writeU32(chunkHdr, 4, fb->len);
            fwrite(chunkHdr, 1, 8, aviFile);
            fwrite(fb->buf, 1, fb->len, aviFile);
            if (fb->len & 1) {
                uint8_t pad = 0;
                fwrite(&pad, 1, 1, aviFile);
                dataSize += 8 + fb->len + 1;
            } else {
                dataSize += 8 + fb->len;
            }
            frameCount++;

            xSemaphoreTake(g_camera_mutex, portMAX_DELAY);
            esp_camera_fb_return(fb);
            xSemaphoreGive(g_camera_mutex);

            if (frameCount % 30 == 0) {
                uint32_t elapsed = (millis() - startTime - pausedMs) / 1000;
                float fps = (elapsed > 0) ? (float)frameCount / elapsed : 0;
                Serial.printf("[REC TASK] %ds | Frames: %d | FPS: %.1f | Dropped: %d\n",
                    elapsed, frameCount, fps, droppedFrames);
            }
        }

        // ── Finalize AVI header ───────────────────────────────────────────────
        setLED(255, 165, 0);
        uint32_t durationMs = millis() - startTime - pausedMs;
        float    durationS  = durationMs / 1000.0f;
        float    avgFps     = (durationS > 0) ? (float)frameCount / durationS : 1;
        uint32_t finalFps   = max((uint32_t)avgFps, (uint32_t)1);

        uint8_t finalHeader[AVI_HEADER_SIZE];
        buildAviHeader(finalHeader, finalFps, frameCount, dataSize);
        fseek(aviFile, 0, SEEK_SET);
        fwrite(finalHeader, 1, AVI_HEADER_SIZE, aviFile);
        fclose(aviFile);
        aviFile = NULL;
        Serial.printf("[REC TASK] Clip finalized: %d frames @ %.1f fps\n",
                      frameCount, avgFps);

        // ── Photo interrupted: photo FIRST, then upload partial AVI ──────────
        if (photoInterrupted) {
            g_take_photo = false;
            Serial.println("[REC TASK] Taking photo before uploading partial clip...");
            doPhotoCapture();

            if (frameCount > 0 && WiFi.status() == WL_CONNECTED) {
                setLED(0, 255, 0);
                Serial.println("[REC TASK] Uploading partial clip...");
                bool uploaded = uploadFile(VIDEO_PATH);
                if (uploaded) {
                    setLED(0, 200, 255);
                    String decision = waitForCommand();
                    if (decision == "delete") {
                        remove(VIDEO_PATH);
                        Serial.println("[REC TASK] Partial clip deleted");
                    } else if (decision == "format_sd") {
                        formatSD();
                    } else {
                        Serial.println("[REC TASK] Partial clip kept");
                    }
                } else {
                    Serial.println("[REC TASK] Partial clip upload failed");
                }
            }
            continue;
        }

        // ── Normal flow: upload full clip ─────────────────────────────────────
        if (frameCount > 0 && WiFi.status() == WL_CONNECTED) {
            setLED(0, 255, 0);
            Serial.println("[REC TASK] Uploading full clip...");
            bool uploaded = uploadFile(VIDEO_PATH);
            if (uploaded) {
                setLED(0, 200, 255);
                String decision = waitForCommand();
                if (decision == "delete") {
                    remove(VIDEO_PATH);
                    Serial.println("[REC TASK] File deleted");
                } else if (decision == "format_sd") {
                    formatSD();
                } else {
                    Serial.println("[REC TASK] File kept");
                }
            } else {
                Serial.println("[REC TASK] Upload failed");
            }
        }
    }
}
// ── Core 0 — Pause listener task ─────────────────────────────────────────────
void pauseListenerTask(void* pvParameters) {
    Serial.printf("[PAUSE TASK] Listening on port 5007 (Core %d)\n",
                  xPortGetCoreID());
    while (true) {
        WiFiClient client = pauseCmdServer.available();
        if (client) {
            String cmd = "";
            long timeout = millis() + 5000;
            while (millis() < timeout) {
                while (client.available()) {
                    char c = client.read();
                    if (c == '\n') goto done;
                    cmd += c;
                }
                vTaskDelay(pdMS_TO_TICKS(10));
            }
            done:
            cmd.trim();
            client.stop();
            Serial.printf("[PAUSE TASK] Received: %s\n", cmd.c_str());
            if (cmd == "pause") {
                g_paused = true;
                setLED(255, 255, 0);
                Serial.println("[PAUSE TASK] Paused!");
            } else if (cmd == "resume") {
                g_paused = false;
                setLED(255, 0, 0);
                Serial.println("[PAUSE TASK] Resumed!");
            }
        }
        vTaskDelay(pdMS_TO_TICKS(50));
    }
}



// ── Setup ─────────────────────────────────────────────────────────────────────
void setup() {
    delay(5000);
    USB.begin();
    Serial.begin(115200);
    unsigned long t = millis();
    while (!Serial && millis() - t < 10000) delay(10);
    delay(2000);
    Serial.println("BOOT OK");

    g_camera_mutex = xSemaphoreCreateMutex();

    setLED(255, 255, 255);
    Serial.printf("[WIFI] Connecting to %s...\n", ssid);
    WiFi.begin(ssid, password);
    int wifiTries = 0;
    while (WiFi.status() != WL_CONNECTED && wifiTries < 40) {
        delay(500);
        Serial.print(".");
        wifiTries++;
    }
    if (WiFi.status() == WL_CONNECTED) {
        WiFi.setSleep(false);
        Serial.printf("\n[WIFI] Connected! IP: %s\n", WiFi.localIP().toString().c_str());
    } else {
        Serial.println("\n[WIFI] Failed");
    }

    Serial.println("[SD] Initializing...");
    sdmmc_host_t host = SDMMC_HOST_DEFAULT();
    host.max_freq_khz = SDMMC_FREQ_DEFAULT;
    sdmmc_slot_config_t slot = SDMMC_SLOT_CONFIG_DEFAULT();
    slot.width = 1;
    slot.clk   = (gpio_num_t)39;
    slot.cmd   = (gpio_num_t)38;
    slot.d0    = (gpio_num_t)40;
    esp_vfs_fat_sdmmc_mount_config_t mount_cfg = {
        .format_if_mount_failed = false,
        .max_files              = 5,
        .allocation_unit_size   = 16 * 1024
    };
    esp_err_t ret = esp_vfs_fat_sdmmc_mount("/sdcard", &host, &slot, &mount_cfg, &card);
    if (ret != ESP_OK) {
        Serial.printf("[SD] Mount failed: %s\n", esp_err_to_name(ret));
        setLED(255, 0, 0);
        while (true) delay(1000);
    }
    Serial.println("[SD] Mounted OK");

    if (!initCameraVideo()) {
        Serial.println("[CAM] Init failed — halting");
        setLED(255, 0, 0);
        while (true) delay(1000);
    }
    Serial.println("[CAM] Initialized OK");

    photoCmdServer.begin();
    Serial.printf("[PHOTO] Listening for take_photo on port %d\n", PHOTO_CMD_PORT);

    pauseCmdServer.begin();
    Serial.println("[PAUSE] Listening for pause/resume on port 5007");

    xTaskCreatePinnedToCore(
        photoListenerTask, "PhotoListener",
        4096, NULL, 1, NULL, 0);   // Core 0

    xTaskCreatePinnedToCore(
        pauseListenerTask, "PauseListener",
        4096, NULL, 1, NULL, 0);   // Core 0

    xTaskCreatePinnedToCore(
        recordingTask, "Recording",
        8192, NULL, 1, NULL, 1);

    Serial.println("[SETUP] Both tasks launched.");
}

// ── Loop ──────────────────────────────────────────────────────────────────────
void loop() {
    vTaskDelay(pdMS_TO_TICKS(1000));
}
