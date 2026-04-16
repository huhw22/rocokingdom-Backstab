// ntp_window_clicker_win32.cpp
// Fixed version:
// - Stop logic uses a manual-reset event to interrupt waiting immediately
// - PreciseWaitUntil is interruptible
// - StopScheduler cleans up based on joinable(), not only g_running
// - NTP socket timeout reduced to make stop more responsive even during sync

#ifndef UNICODE
#define UNICODE
#endif
#ifndef _UNICODE
#define _UNICODE
#endif

#include <winsock2.h>
#include <windows.h>
#include <commctrl.h>
#include <ws2tcpip.h>
#include <shellapi.h>

#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cwchar>
#include <iomanip>
#include <memory>
#include <mutex>
#include <set>
#include <sstream>
#include <string>
#include <thread>
#include <vector>
#include <algorithm>

#pragma comment(lib, "comctl32.lib")
#pragma comment(lib, "ws2_32.lib")
#pragma comment(lib, "shell32.lib")

using namespace std::chrono;

static const wchar_t* APP_TITLE = L"Rocokingdom backstab clicker";

enum ControlId {
    IDC_COMBO_WINDOWS = 1001,
    IDC_BTN_REFRESH   = 1002,
    IDC_EDIT_X        = 1003,
    IDC_EDIT_Y        = 1004,
    IDC_BTN_CAPTURE   = 1005,
    IDC_EDIT_MINUTES  = 1006,
    IDC_EDIT_NTP      = 1007,
    IDC_BTN_START     = 1008,
    IDC_BTN_STOP      = 1009,
    IDC_BTN_TEST      = 1010,
    IDC_LOG           = 1011,
    IDC_CHK_RESTORE   = 1012,
    IDC_STATIC_STATUS = 1013,
};

static const UINT WM_APP_LOG          = WM_APP + 1;
static const UINT WM_APP_CAPTURE_DONE = WM_APP + 2;
static const UINT WM_APP_STATUS       = WM_APP + 3;

struct WindowItem {
    HWND hwnd = nullptr;
    std::wstring text;
};

struct AppConfig {
    HWND targetHwnd = nullptr;
    int clickX = 0;
    int clickY = 0;
    std::vector<int> minuteMarks;   // minute marks inside each 10-minute block, e.g. [1,3,7]
    std::wstring ntpServer = L"ntp.tuna.tsinghua.edu.cn";
    bool restoreCursor = true;
};

struct CaptureResult {
    bool ok = false;
    int x = 0;
    int y = 0;
    std::wstring msg;
};

static HINSTANCE g_hInst = nullptr;
static HWND g_hWnd = nullptr;
static HWND g_comboWindows = nullptr;
static HWND g_editX = nullptr;
static HWND g_editY = nullptr;
static HWND g_editMinutes = nullptr;
static HWND g_editNtp = nullptr;
static HWND g_log = nullptr;
static HWND g_chkRestore = nullptr;
static HWND g_status = nullptr;

static std::vector<WindowItem> g_windows;
static std::mutex g_windowsMutex;

static std::atomic<bool> g_running{false};
static std::thread g_workerThread;
static HANDLE g_stopEvent = nullptr;

static std::atomic<bool> g_captureRunning{false};

static std::mutex g_ntpMutex;
static nanoseconds g_ntpOffset = nanoseconds::zero();
static bool g_hasNtpOffset = false;

static std::wstring Utf8ToWide(const std::string& s) {
    if (s.empty()) return L"";
    int len = MultiByteToWideChar(CP_UTF8, 0, s.data(), (int)s.size(), nullptr, 0);
    std::wstring out(len, L'\0');
    MultiByteToWideChar(CP_UTF8, 0, s.data(), (int)s.size(), out.data(), len);
    return out;
}

static std::string WideToUtf8(const std::wstring& s) {
    if (s.empty()) return "";
    int len = WideCharToMultiByte(CP_UTF8, 0, s.data(), (int)s.size(), nullptr, 0, nullptr, nullptr);
    std::string out(len, '\0');
    WideCharToMultiByte(CP_UTF8, 0, s.data(), (int)s.size(), out.data(), len, nullptr, nullptr);
    return out;
}

static void PostLog(const std::wstring& msg) {
    auto p = new std::wstring(msg);
    PostMessageW(g_hWnd, WM_APP_LOG, 0, (LPARAM)p);
}

static void PostStatus(const std::wstring& msg) {
    auto p = new std::wstring(msg);
    PostMessageW(g_hWnd, WM_APP_STATUS, 0, (LPARAM)p);
}

static std::wstring LocalTimestampString() {
    SYSTEMTIME st{};
    GetLocalTime(&st);
    wchar_t buf[64];
    swprintf(buf, 64, L"[%02u:%02u:%02u.%03u] ", st.wHour, st.wMinute, st.wSecond, st.wMilliseconds);
    return buf;
}

static void AppendLogNow(const std::wstring& msg) {
    std::wstring line = LocalTimestampString() + msg + L"\r\n";
    int len = GetWindowTextLengthW(g_log);
    SendMessageW(g_log, EM_SETSEL, (WPARAM)len, (LPARAM)len);
    SendMessageW(g_log, EM_REPLACESEL, FALSE, (LPARAM)line.c_str());
    SendMessageW(g_log, EM_SCROLLCARET, 0, 0);
}

static bool GetEditInt(HWND hEdit, int& out) {
    wchar_t buf[64];
    GetWindowTextW(hEdit, buf, 64);
    wchar_t* end = nullptr;
    long v = wcstol(buf, &end, 10);
    if (end == buf) return false;
    out = (int)v;
    return true;
}

static std::wstring GetWindowTextString(HWND h) {
    int len = GetWindowTextLengthW(h);
    std::wstring s(len, L'\0');
    GetWindowTextW(h, s.data(), len + 1);
    return s;
}

static void SetEditInt(HWND hEdit, int v) {
    wchar_t buf[32];
    swprintf(buf, 32, L"%d", v);
    SetWindowTextW(hEdit, buf);
}

static std::vector<int> ParseMinuteMarks(const std::wstring& s, std::wstring& err) {
    std::set<int> uniq;
    std::wstring token;
    for (size_t i = 0; i <= s.size(); ++i) {
        wchar_t ch = (i < s.size()) ? s[i] : L',';
        if (ch == L',' || ch == L' ' || ch == L';' || ch == L'，' || ch == L'；' || i == s.size()) {
            if (!token.empty()) {
                wchar_t* end = nullptr;
                long v = wcstol(token.c_str(), &end, 10);
                if (end == token.c_str() || *end != L'\0') {
                    err = L"分钟列表解析失败，请使用类似 1,3,7";
                    return {};
                }
                if (v < 0 || v > 9) {
                    err = L"分钟列表中的每个值必须在 0~9 之间";
                    return {};
                }
                uniq.insert((int)v);
                token.clear();
            }
        } else {
            token.push_back(ch);
        }
    }
    if (uniq.empty()) {
        err = L"分钟列表不能为空";
        return {};
    }
    return std::vector<int>(uniq.begin(), uniq.end());
}

static BOOL CALLBACK EnumWindowsProc(HWND hwnd, LPARAM) {
    if (!IsWindowVisible(hwnd)) return TRUE;
    if (GetWindow(hwnd, GW_OWNER) != nullptr) return TRUE;

    int len = GetWindowTextLengthW(hwnd);
    if (len <= 0) return TRUE;

    wchar_t title[512];
    GetWindowTextW(hwnd, title, 512);

    RECT rc{};
    if (!GetWindowRect(hwnd, &rc)) return TRUE;
    if (rc.right <= rc.left || rc.bottom <= rc.top) return TRUE;

    std::wstringstream ss;
    ss << title << L"   [HWND=0x" << std::hex << std::uppercase << (uintptr_t)hwnd << L"]";
    WindowItem item;
    item.hwnd = hwnd;
    item.text = ss.str();

    g_windows.push_back(std::move(item));
    return TRUE;
}

static void RefreshWindowsList() {
    std::lock_guard<std::mutex> lock(g_windowsMutex);
    g_windows.clear();
    EnumWindows(EnumWindowsProc, 0);

    SendMessageW(g_comboWindows, CB_RESETCONTENT, 0, 0);
    for (const auto& it : g_windows) {
        SendMessageW(g_comboWindows, CB_ADDSTRING, 0, (LPARAM)it.text.c_str());
    }
    if (!g_windows.empty()) {
        SendMessageW(g_comboWindows, CB_SETCURSEL, 0, 0);
    }
    AppendLogNow(L"窗口列表已刷新");
}

static HWND GetSelectedTargetWindow() {
    int idx = (int)SendMessageW(g_comboWindows, CB_GETCURSEL, 0, 0);
    std::lock_guard<std::mutex> lock(g_windowsMutex);
    if (idx < 0 || idx >= (int)g_windows.size()) return nullptr;
    return g_windows[idx].hwnd;
}

static bool ValidateClientPoint(HWND hwnd, int x, int y, std::wstring& err) {
    RECT rc{};
    if (!GetClientRect(hwnd, &rc)) {
        err = L"无法获取目标窗口客户区大小";
        return false;
    }
    if (x < 0 || y < 0 || x >= (rc.right - rc.left) || y >= (rc.bottom - rc.top)) {
        std::wstringstream ss;
        ss << L"坐标超出客户区范围，当前客户区大小约为 "
           << (rc.right - rc.left) << L"x" << (rc.bottom - rc.top);
        err = ss.str();
        return false;
    }
    return true;
}

static bool SendRealMouseClick(HWND hwnd, int clientX, int clientY, bool restoreCursor, std::wstring& err) {
    if (!IsWindow(hwnd)) {
        err = L"目标窗口无效";
        return false;
    }

    POINT pt{ clientX, clientY };
    if (!ClientToScreen(hwnd, &pt)) {
        err = L"ClientToScreen 失败";
        return false;
    }

    POINT oldPt{};
    if (restoreCursor) {
        GetCursorPos(&oldPt);
    }

    ShowWindow(hwnd, SW_RESTORE);
    SetForegroundWindow(hwnd);
    BringWindowToTop(hwnd);
    SetActiveWindow(hwnd);

    if (!SetCursorPos(pt.x, pt.y)) {
        err = L"SetCursorPos 失败";
        return false;
    }

    Sleep(15);

    INPUT inputs[2]{};
    inputs[0].type = INPUT_MOUSE;
    inputs[0].mi.dwFlags = MOUSEEVENTF_LEFTDOWN;
    inputs[1].type = INPUT_MOUSE;
    inputs[1].mi.dwFlags = MOUSEEVENTF_LEFTUP;

    UINT sent = SendInput(2, inputs, sizeof(INPUT));
    if (sent != 2) {
        err = L"SendInput 失败";
        return false;
    }

    if (restoreCursor) {
        Sleep(15);
        SetCursorPos(oldPt.x, oldPt.y);
    }
    return true;
}

static uint32_t ReadBE32(const uint8_t* p) {
    return (uint32_t(p[0]) << 24) | (uint32_t(p[1]) << 16) | (uint32_t(p[2]) << 8) | uint32_t(p[3]);
}

static system_clock::time_point NtpToTimePoint(uint32_t seconds1900, uint32_t frac) {
    static const uint64_t NTP_TO_UNIX = 2208988800ULL;
    int64_t unixSec = (int64_t)seconds1900 - (int64_t)NTP_TO_UNIX;
    uint64_t ns = ((uint64_t)frac * 1000000000ULL) >> 32;
    return system_clock::time_point(seconds(unixSec) + nanoseconds(ns));
}

static bool QueryNtpOffset(const std::wstring& serverW, nanoseconds& outOffset, std::wstring& err) {
    std::string server = WideToUtf8(serverW);

    addrinfo hints{};
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_DGRAM;
    hints.ai_protocol = IPPROTO_UDP;

    addrinfo* res = nullptr;
    int gai = getaddrinfo(server.c_str(), "123", &hints, &res);
    if (gai != 0 || !res) {
        err = L"getaddrinfo 失败";
        return false;
    }

    SOCKET s = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
    if (s == INVALID_SOCKET) {
        freeaddrinfo(res);
        err = L"socket 创建失败";
        return false;
    }

    DWORD timeoutMs = 300;
    setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, (const char*)&timeoutMs, sizeof(timeoutMs));
    setsockopt(s, SOL_SOCKET, SO_SNDTIMEO, (const char*)&timeoutMs, sizeof(timeoutMs));

    uint8_t packet[48]{};
    packet[0] = 0x1B; // LI=0, VN=3, Mode=3 (client)

    auto t0 = system_clock::now();
    int sent = sendto(s, (const char*)packet, 48, 0, res->ai_addr, (int)res->ai_addrlen);
    if (sent != 48) {
        closesocket(s);
        freeaddrinfo(res);
        err = L"sendto 失败";
        return false;
    }

    sockaddr_storage from{};
    int fromlen = sizeof(from);
    uint8_t recvbuf[48]{};
    int recvd = recvfrom(s, (char*)recvbuf, 48, 0, (sockaddr*)&from, &fromlen);
    auto t3 = system_clock::now();

    closesocket(s);
    freeaddrinfo(res);

    if (recvd < 48) {
        err = L"NTP 响应超时或长度异常";
        return false;
    }

    uint32_t rxSec  = ReadBE32(recvbuf + 32);
    uint32_t rxFrac = ReadBE32(recvbuf + 36);
    uint32_t txSec  = ReadBE32(recvbuf + 40);
    uint32_t txFrac = ReadBE32(recvbuf + 44);

    auto t1 = NtpToTimePoint(rxSec, rxFrac);
    auto t2 = NtpToTimePoint(txSec, txFrac);

    auto part1 = t1 - t0;
    auto part2 = t2 - t3;
    outOffset = duration_cast<nanoseconds>((part1 + part2) / 2);
    return true;
}

static system_clock::time_point CorrectedNow() {
    std::lock_guard<std::mutex> lock(g_ntpMutex);
    return system_clock::now() + g_ntpOffset;
}

static bool RefreshNtpOffset(const std::wstring& server, bool logOk, bool logFail) {
    nanoseconds off{};
    std::wstring err;
    bool ok = QueryNtpOffset(server, off, err);
    {
        std::lock_guard<std::mutex> lock(g_ntpMutex);
        if (ok) {
            g_ntpOffset = off;
            g_hasNtpOffset = true;
        }
    }
    if (ok && logOk) {
        auto ms = duration_cast<milliseconds>(off).count();
        std::wstringstream ss;
        ss << L"NTP 授时成功，当前时钟偏移约 " << ms << L" ms";
        PostLog(ss.str());
    } else if (!ok && logFail) {
        PostLog(L"NTP 授时失败，将继续使用上次偏移或本机时间");
    }
    return ok;
}

static std::wstring FormatTimePointLocal(const system_clock::time_point& tp) {
    auto tt = system_clock::to_time_t(tp);
    tm localTm{};
    localtime_s(&localTm, &tt);
    auto ms = duration_cast<milliseconds>(tp.time_since_epoch()).count() % 1000;
    wchar_t buf[64];
    swprintf(buf, 64, L"%04d-%02d-%02d %02d:%02d:%02d.%03lld",
             localTm.tm_year + 1900, localTm.tm_mon + 1, localTm.tm_mday,
             localTm.tm_hour, localTm.tm_min, localTm.tm_sec, (long long)ms);
    return buf;
}

static system_clock::time_point ComputeNextTrigger(const system_clock::time_point& now, const std::vector<int>& marks) {
    auto tt = system_clock::to_time_t(now);
    tm localTm{};
    localtime_s(&localTm, &tt);

    tm base = localTm;
    base.tm_sec = 0;
    int blockBase = (base.tm_min / 10) * 10;
    base.tm_min = blockBase;

    for (int blk = 0; blk < 24 * 6 * 2; ++blk) {
        for (int m : marks) {
            tm cand = base;
            cand.tm_min = blockBase + blk * 10 + m;
            cand.tm_sec = 0;
            time_t ctt = mktime(&cand);
            auto tp = system_clock::from_time_t(ctt);
            if (tp > now + milliseconds(1)) {
                return tp;
            }
        }
    }
    return now + minutes(10);
}

static bool StopRequested() {
    return g_stopEvent && WaitForSingleObject(g_stopEvent, 0) == WAIT_OBJECT_0;
}

static bool PreciseWaitUntil(const system_clock::time_point& target) {
    while (g_running.load()) {
        if (StopRequested()) {
            return false;
        }

        auto now = CorrectedNow();
        auto diff = target - now;
        if (diff <= milliseconds(0)) {
            return true;
        }

        if (diff > milliseconds(200)) {
            auto remain = duration_cast<milliseconds>(diff - milliseconds(100));
            DWORD waitMs = (DWORD)std::min<long long>(remain.count(), 500);
            if (WaitForSingleObject(g_stopEvent, waitMs) == WAIT_OBJECT_0) {
                return false;
            }
        } else if (diff > milliseconds(20)) {
            if (WaitForSingleObject(g_stopEvent, 5) == WAIT_OBJECT_0) {
                return false;
            }
        } else if (diff > milliseconds(3)) {
            if (WaitForSingleObject(g_stopEvent, 1) == WAIT_OBJECT_0) {
                return false;
            }
        } else {
            while (g_running.load() && CorrectedNow() < target) {
                if (StopRequested()) {
                    return false;
                }
                YieldProcessor();
            }
            return g_running.load() && !StopRequested();
        }
    }
    return false;
}

static bool ReadConfigFromUi(AppConfig& cfg, std::wstring& err) {
    cfg.targetHwnd = GetSelectedTargetWindow();
    if (!cfg.targetHwnd || !IsWindow(cfg.targetHwnd)) {
        err = L"请先选择一个有效窗口";
        return false;
    }

    if (!GetEditInt(g_editX, cfg.clickX) || !GetEditInt(g_editY, cfg.clickY)) {
        err = L"X/Y 坐标无效";
        return false;
    }

    std::wstring minuteText = GetWindowTextString(g_editMinutes);
    cfg.minuteMarks = ParseMinuteMarks(minuteText, err);
    if (cfg.minuteMarks.empty()) return false;

    cfg.ntpServer = GetWindowTextString(g_editNtp);
    if (cfg.ntpServer.empty()) cfg.ntpServer = L"ntp.tuna.tsinghua.edu.cn";

    cfg.restoreCursor = (SendMessageW(g_chkRestore, BM_GETCHECK, 0, 0) == BST_CHECKED);

    if (!ValidateClientPoint(cfg.targetHwnd, cfg.clickX, cfg.clickY, err)) {
        return false;
    }
    return true;
}

static void SchedulerThreadProc(AppConfig cfg) {
    PostStatus(L"运行中");
    RefreshNtpOffset(cfg.ntpServer, true, true);

    system_clock::time_point lastAnnounced{};
    auto lastSync = steady_clock::now();

    while (g_running.load() && !StopRequested()) {
        if (steady_clock::now() - lastSync > seconds(60)) {
            RefreshNtpOffset(cfg.ntpServer, true, false);
            lastSync = steady_clock::now();
            if (StopRequested()) break;
        }

        auto now = CorrectedNow();
        auto nextTp = ComputeNextTrigger(now, cfg.minuteMarks);

        if (nextTp != lastAnnounced) {
            std::wstringstream ss;
            ss << L"下一次点击时间: " << FormatTimePointLocal(nextTp);
            PostLog(ss.str());
            lastAnnounced = nextTp;
        }

        if (!PreciseWaitUntil(nextTp)) {
            break;
        }

        if (!g_running.load() || StopRequested()) {
            break;
        }

        std::wstring err;
        bool ok = SendRealMouseClick(cfg.targetHwnd, cfg.clickX, cfg.clickY, cfg.restoreCursor, err);
        auto fired = CorrectedNow();

        if (ok) {
            std::wstringstream ss;
            ss << L"已点击，触发时间: " << FormatTimePointLocal(fired)
               << L"  目标坐标=(" << cfg.clickX << L"," << cfg.clickY << L")";
            PostLog(ss.str());
        } else {
            PostLog(L"点击失败: " + err);
        }

        if (WaitForSingleObject(g_stopEvent, 150) == WAIT_OBJECT_0) {
            break;
        }
    }

    g_running = false;
    PostStatus(L"已停止");
}

static void StartScheduler() {
    if (g_workerThread.joinable()) {
        g_running = false;
        if (g_stopEvent) SetEvent(g_stopEvent);
        g_workerThread.join();
    }

    if (g_running.load()) {
        AppendLogNow(L"当前已经在运行");
        return;
    }

    AppConfig cfg;
    std::wstring err;
    if (!ReadConfigFromUi(cfg, err)) {
        AppendLogNow(L"启动失败: " + err);
        return;
    }

    if (!g_stopEvent) {
        AppendLogNow(L"启动失败: 停止事件未初始化");
        return;
    }

    ResetEvent(g_stopEvent);
    g_running = true;
    g_workerThread = std::thread(SchedulerThreadProc, cfg);
    AppendLogNow(L"调度已启动");
}

static void StopScheduler() {
    bool wasRunning = g_running.exchange(false);

    if (g_stopEvent) {
        SetEvent(g_stopEvent);
    }

    if (g_workerThread.joinable()) {
        g_workerThread.join();
    }

    if (wasRunning) {
        AppendLogNow(L"调度已停止");
    }
}

static void TestClickOnce() {
    AppConfig cfg;
    std::wstring err;
    if (!ReadConfigFromUi(cfg, err)) {
        AppendLogNow(L"测试失败: " + err);
        return;
    }
    bool ok = SendRealMouseClick(cfg.targetHwnd, cfg.clickX, cfg.clickY, cfg.restoreCursor, err);
    if (ok) AppendLogNow(L"测试点击完成");
    else AppendLogNow(L"测试点击失败: " + err);
}

static void StartCapturePoint() {
    if (g_captureRunning.exchange(true)) {
        AppendLogNow(L"当前已有取点任务在进行");
        return;
    }

    HWND hwndTarget = GetSelectedTargetWindow();
    if (!hwndTarget || !IsWindow(hwndTarget)) {
        g_captureRunning = false;
        AppendLogNow(L"请先选择目标窗口");
        return;
    }

    AppendLogNow(L"3 秒后将读取当前鼠标在目标窗口客户区中的位置，请把鼠标移到目标点");

    std::thread([hwndTarget]() {
        Sleep(3000);
        auto result = new CaptureResult();
        POINT p{};
        if (!GetCursorPos(&p)) {
            result->ok = false;
            result->msg = L"GetCursorPos 失败";
        } else {
            POINT cp = p;
            if (!ScreenToClient(hwndTarget, &cp)) {
                result->ok = false;
                result->msg = L"ScreenToClient 失败";
            } else {
                std::wstring err;
                if (!ValidateClientPoint(hwndTarget, cp.x, cp.y, err)) {
                    result->ok = false;
                    result->msg = L"鼠标不在目标窗口客户区内: " + err;
                } else {
                    result->ok = true;
                    result->x = cp.x;
                    result->y = cp.y;
                    std::wstringstream ss;
                    ss << L"已取点: (" << cp.x << L"," << cp.y << L")";
                    result->msg = ss.str();
                }
            }
        }
        PostMessageW(g_hWnd, WM_APP_CAPTURE_DONE, 0, (LPARAM)result);
    }).detach();
}

static void CreateUi(HWND hwnd) {
    HFONT hFont = (HFONT)GetStockObject(DEFAULT_GUI_FONT);

    CreateWindowW(L"STATIC", L"目标窗口:", WS_CHILD | WS_VISIBLE,
                  12, 12, 72, 22, hwnd, nullptr, g_hInst, nullptr);
    g_comboWindows = CreateWindowW(WC_COMBOBOXW, L"",
                  WS_CHILD | WS_VISIBLE | WS_TABSTOP | CBS_DROPDOWNLIST | WS_VSCROLL,
                  84, 10, 520, 240, hwnd, (HMENU)IDC_COMBO_WINDOWS, g_hInst, nullptr);
    CreateWindowW(L"BUTTON", L"刷新窗口列表",
                  WS_CHILD | WS_VISIBLE | WS_TABSTOP,
                  614, 10, 120, 26, hwnd, (HMENU)IDC_BTN_REFRESH, g_hInst, nullptr);

    CreateWindowW(L"STATIC", L"客户区 X:", WS_CHILD | WS_VISIBLE,
                  12, 50, 72, 22, hwnd, nullptr, g_hInst, nullptr);
    g_editX = CreateWindowW(L"EDIT", L"0",
                  WS_CHILD | WS_VISIBLE | WS_TABSTOP | WS_BORDER | ES_AUTOHSCROLL,
                  84, 48, 80, 24, hwnd, (HMENU)IDC_EDIT_X, g_hInst, nullptr);

    CreateWindowW(L"STATIC", L"客户区 Y:", WS_CHILD | WS_VISIBLE,
                  180, 50, 72, 22, hwnd, nullptr, g_hInst, nullptr);
    g_editY = CreateWindowW(L"EDIT", L"0",
                  WS_CHILD | WS_VISIBLE | WS_TABSTOP | WS_BORDER | ES_AUTOHSCROLL,
                  252, 48, 80, 24, hwnd, (HMENU)IDC_EDIT_Y, g_hInst, nullptr);

    CreateWindowW(L"BUTTON", L"倒计时后取鼠标位置",
                  WS_CHILD | WS_VISIBLE | WS_TABSTOP,
                  350, 46, 180, 28, hwnd, (HMENU)IDC_BTN_CAPTURE, g_hInst, nullptr);

    g_chkRestore = CreateWindowW(L"BUTTON", L"点击后恢复鼠标位置",
                  WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_AUTOCHECKBOX,
                  550, 50, 180, 22, hwnd, (HMENU)IDC_CHK_RESTORE, g_hInst, nullptr);
    SendMessageW(g_chkRestore, BM_SETCHECK, BST_CHECKED, 0);

    CreateWindowW(L"STATIC", L"每10分钟块内触发分钟:", WS_CHILD | WS_VISIBLE,
                  12, 90, 150, 22, hwnd, nullptr, g_hInst, nullptr);
    g_editMinutes = CreateWindowW(L"EDIT", L"1,3,7",
                  WS_CHILD | WS_VISIBLE | WS_TABSTOP | WS_BORDER | ES_AUTOHSCROLL,
                  162, 88, 170, 24, hwnd, (HMENU)IDC_EDIT_MINUTES, g_hInst, nullptr);

    CreateWindowW(L"STATIC", L"NTP 服务器:", WS_CHILD | WS_VISIBLE,
                  350, 90, 90, 22, hwnd, nullptr, g_hInst, nullptr);
    g_editNtp = CreateWindowW(L"EDIT", L"ntp.tuna.tsinghua.edu.cn",
                  WS_CHILD | WS_VISIBLE | WS_TABSTOP | WS_BORDER | ES_AUTOHSCROLL,
                  440, 88, 294, 24, hwnd, (HMENU)IDC_EDIT_NTP, g_hInst, nullptr);

    CreateWindowW(L"BUTTON", L"开始",
                  WS_CHILD | WS_VISIBLE | WS_TABSTOP,
                  12, 128, 90, 30, hwnd, (HMENU)IDC_BTN_START, g_hInst, nullptr);
    CreateWindowW(L"BUTTON", L"停止",
                  WS_CHILD | WS_VISIBLE | WS_TABSTOP,
                  112, 128, 90, 30, hwnd, (HMENU)IDC_BTN_STOP, g_hInst, nullptr);
    CreateWindowW(L"BUTTON", L"测试点击一次",
                  WS_CHILD | WS_VISIBLE | WS_TABSTOP,
                  212, 128, 120, 30, hwnd, (HMENU)IDC_BTN_TEST, g_hInst, nullptr);

    g_status = CreateWindowW(L"STATIC", L"未运行",
                  WS_CHILD | WS_VISIBLE,
                  350, 132, 200, 22, hwnd, (HMENU)IDC_STATIC_STATUS, g_hInst, nullptr);

    g_log = CreateWindowW(L"EDIT", L"",
                  WS_CHILD | WS_VISIBLE | WS_VSCROLL | WS_BORDER |
                  ES_LEFT | ES_MULTILINE | ES_AUTOVSCROLL | ES_READONLY,
                  12, 170, 722, 300, hwnd, (HMENU)IDC_LOG, g_hInst, nullptr);

    for (HWND h : {g_comboWindows, g_editX, g_editY, g_editMinutes, g_editNtp, g_log, g_chkRestore, g_status}) {
        SendMessageW(h, WM_SETFONT, (WPARAM)hFont, TRUE);
    }

    RefreshWindowsList();
    AppendLogNow(L"程序已启动。说明：分钟列表 1,3,7 表示在每个 10 分钟周期的第 1/3/7 分钟整秒触发点击。");
}

static LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    switch (msg) {
    case WM_CREATE:
        CreateUi(hwnd);
        return 0;

    case WM_COMMAND:
        switch (LOWORD(wParam)) {
        case IDC_BTN_REFRESH:
            RefreshWindowsList();
            return 0;
        case IDC_BTN_CAPTURE:
            StartCapturePoint();
            return 0;
        case IDC_BTN_START:
            StartScheduler();
            return 0;
        case IDC_BTN_STOP:
            StopScheduler();
            return 0;
        case IDC_BTN_TEST:
            TestClickOnce();
            return 0;
        default:
            break;
        }
        break;

    case WM_APP_LOG: {
        std::unique_ptr<std::wstring> p((std::wstring*)lParam);
        if (p) AppendLogNow(*p);
        return 0;
    }

    case WM_APP_STATUS: {
        std::unique_ptr<std::wstring> p((std::wstring*)lParam);
        if (p) SetWindowTextW(g_status, p->c_str());
        return 0;
    }

    case WM_APP_CAPTURE_DONE: {
        std::unique_ptr<CaptureResult> p((CaptureResult*)lParam);
        g_captureRunning = false;
        if (p) {
            if (p->ok) {
                SetEditInt(g_editX, p->x);
                SetEditInt(g_editY, p->y);
            }
            AppendLogNow(p->msg);
        }
        return 0;
    }

    case WM_CLOSE:
        StopScheduler();
        DestroyWindow(hwnd);
        return 0;

    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;

    default:
        break;
    }
    return DefWindowProcW(hwnd, msg, wParam, lParam);
}

int WINAPI wWinMain(HINSTANCE hInstance, HINSTANCE, PWSTR, int nCmdShow) {
    g_hInst = hInstance;

    WSADATA wsa{};
    if (WSAStartup(MAKEWORD(2, 2), &wsa) != 0) {
        MessageBoxW(nullptr, L"WSAStartup 失败", APP_TITLE, MB_ICONERROR);
        return 1;
    }

    g_stopEvent = CreateEventW(nullptr, TRUE, FALSE, nullptr);
    if (!g_stopEvent) {
        MessageBoxW(nullptr, L"CreateEventW 失败", APP_TITLE, MB_ICONERROR);
        WSACleanup();
        return 1;
    }

    INITCOMMONCONTROLSEX icc{};
    icc.dwSize = sizeof(icc);
    icc.dwICC = ICC_WIN95_CLASSES;
    InitCommonControlsEx(&icc);

    WNDCLASSEXW wc{};
    wc.cbSize = sizeof(wc);
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInstance;
    wc.lpszClassName = L"NtpWindowClickerWin32Cls";
    wc.hCursor = LoadCursor(nullptr, IDC_ARROW);
    wc.hIcon = LoadIcon(nullptr, IDI_APPLICATION);
    wc.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);

    if (!RegisterClassExW(&wc)) {
        MessageBoxW(nullptr, L"RegisterClassExW 失败", APP_TITLE, MB_ICONERROR);
        CloseHandle(g_stopEvent);
        g_stopEvent = nullptr;
        WSACleanup();
        return 1;
    }

    g_hWnd = CreateWindowExW(
        0, wc.lpszClassName, APP_TITLE,
        WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX,
        CW_USEDEFAULT, CW_USEDEFAULT, 760, 530,
        nullptr, nullptr, hInstance, nullptr
    );

    if (!g_hWnd) {
        MessageBoxW(nullptr, L"CreateWindowExW 失败", APP_TITLE, MB_ICONERROR);
        CloseHandle(g_stopEvent);
        g_stopEvent = nullptr;
        WSACleanup();
        return 1;
    }

    ShowWindow(g_hWnd, nCmdShow);
    UpdateWindow(g_hWnd);

    MSG msg{};
    while (GetMessageW(&msg, nullptr, 0, 0)) {
        TranslateMessage(&msg);
        DispatchMessageW(&msg);
    }

    StopScheduler();

    if (g_stopEvent) {
        CloseHandle(g_stopEvent);
        g_stopEvent = nullptr;
    }

    WSACleanup();
    return 0;
}
