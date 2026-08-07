"""ENA 마스코트 — 입력 반응형 데스크탑 캐릭터 (+선택형 작업 타이머).

캐릭터별 파츠 폴더(extract_psd.py로 PSD에서 추출)를 조합해 움직인다:
  python mascot.py                      # 기본 캐릭터 (parts/ = 까만 고양이)
  python mascot.py --char parts_junsa   # 준사 (작업 타이머 포함)
  python mascot.py --preview            # 대표 포즈 PNG 저장 후 종료 (개발용)

동작:
- 키 입력            → 손이 어깨를 축으로 회전하며 키보드를 두드림 (어깨는 몸에 고정)
- 커서 이동/그리기    → 펜 쥔 오른손이 미니 타블렛 화면 위에서 커서를 따라다니고,
                       오른팔은 어깨 고정·손끝 추적으로 치즈스틱처럼 늘어남
- 타이핑만 할 때      → 펜 손·팔은 숨고 '오른팔-타자' 파츠가 나와 양손 타이핑
- 시선/유휴          → 눈동자 커서 추적, 숨쉬기, (마스크 구조가 있으면) 깜빡임
- 타이머(config)     → 캐릭터 위 캡슐 배지에 오늘 작업시간. 입력이 끊기면 휴식 전환.
                       작업일 경계 06:00, 상태는 주기 저장(강제종료 대비).

config.json 주요 키: scale, screen_quad, blink, trail_color, pen_tip,
  hard_alpha(외곽 픽셀 이분화 — 밝은 캐릭터의 검은 테두리 방지),
  timer({"enabled": true, "idle_sec": 60})
조작: 캐릭터 드래그 = 위치 이동, 우클릭 = 메뉴.
"""
import base64 as _b64
import ctypes
import json
import math
import os
import random
import sys
import threading
import time
import tkinter as tk

from PIL import Image, ImageOps, ImageTk

if sys.platform == "darwin":
    # 맥에서는 pynput을 쓰지 않는다. pynput의 맥 리스너는 별도 스레드에서
    # HIToolbox의 TSMGetInputSourceProperty를 호출하는데, macOS 26부터 이 API가
    # 메인 큐 밖 호출을 금지해 앱이 즉사한다 (퀸시 크래시 로그로 확인).
    keyboard = mouse = None
else:
    from pynput import keyboard, mouse

IS_WIN = sys.platform.startswith("win")
IS_MAC = sys.platform == "darwin"

if IS_WIN:
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)  # PER_MONITOR_DPI_AWARE
    except Exception:
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass

_MAC_CG = None
if IS_MAC:                       # 커서·유휴 시간을 얻는 macOS 프레임워크
    try:
        from ctypes import util as _cutil
        _MAC_CG = ctypes.cdll.LoadLibrary(_cutil.find_library("CoreGraphics"))
        _MAC_CG.CGEventSourceSecondsSinceLastEventType.restype = ctypes.c_double
        _MAC_CG.CGEventSourceSecondsSinceLastEventType.argtypes = [
            ctypes.c_uint32, ctypes.c_uint32]
    except Exception:
        _MAC_CG = None

class _MacChromaKey:
    """맥에서 키 색만 화면 합성 단계에 지워 투명하게 만드는 장치.

    Tk 9 는 systemTransparent 를 '칠하지 않음'으로 처리하지 않고 **불투명한 검정**으로
    칠한다. 그래서 NSWindow 를 아무리 투명하게 만들어도(setOpaque_(False) +
    clearColor, 실제로 배경알파 0.00 으로 적용됨) 그 위의 뷰가 검정을 덮어써서 검은
    사각형이 남는다. contentView 의 레이어 배경까지 지워도 마찬가지인데, 검정을
    칠하는 주체가 레이어 배경이 아니라 Tk 의 그리기 자체이기 때문이다.

    그래서 윈도우판과 같은 방법을 쓴다 — 캔버스를 MAC_KEY 로 칠해 두고, 그 색만
    알파 0 으로 바꾸는 색 큐브(CIColorCubeWithColorSpace)를 창 레이어의
    compositingFilter 로 걸어 합성 단계에서 지운다. 색 큐브를 filters 가 아니라
    compositingFilter 로 걸어야 알파 0 이 실제 투명으로 반영된다.

    pyobjc 대신 ctypes 를 쓰는 이유: CIFilter 는 pyobjc-framework-Quartz 에 있는데
    빌드는 Cocoa 만 설치한다. ctypes 면 의존성을 늘리지 않아도 된다.
    """

    N = 64          # 색 큐브 한 변 (64^3 칸)
    RAD = 2         # 이 안쪽은 완전히 투명 (반올림·보간 여유)
    SOFT = 8        # RAD~SOFT 구간은 서서히 불투명해지며 키 색 기운을 빼낸다.
                    # 파츠 색은 키에서 최소 3칸, 대부분 11칸 이상 떨어져 있어
                    # 이 구간에 걸리는 파츠 픽셀은 수백 개 수준이다.

    def __init__(self, key_hex):
        self.err = None
        self.filter = None
        self._keep = []          # 해제되면 안 되는 ObjC 객체를 붙잡아 둔다
        try:
            self._setup(key_hex)
        except Exception as e:
            self.err = repr(e)

    # ── ObjC 최소 브리지 ────────────────────────────────────────────────
    def _setup(self, key_hex):
        self._objc = ctypes.CDLL("/usr/lib/libobjc.dylib")
        for fw in ("AppKit", "QuartzCore", "CoreImage", "CoreGraphics"):
            ctypes.CDLL("/System/Library/Frameworks/%s.framework/%s" % (fw, fw),
                        mode=ctypes.RTLD_GLOBAL)
        self._cg = ctypes.CDLL(
            "/System/Library/Frameworks/CoreGraphics.framework/CoreGraphics")
        self._objc.objc_getClass.restype = ctypes.c_void_p
        self._objc.objc_getClass.argtypes = [ctypes.c_char_p]
        self._objc.sel_registerName.restype = ctypes.c_void_p
        self._objc.sel_registerName.argtypes = [ctypes.c_char_p]
        self._send = ctypes.cast(self._objc.objc_msgSend, ctypes.c_void_p).value
        self.filter = self._build_filter(key_hex)

    def _cls(self, name):
        return self._objc.objc_getClass(name.encode())

    def _sel(self, name):
        return self._objc.sel_registerName(name.encode())

    def _msg(self, obj, name, *args, **kw):
        restype = kw.get("restype", ctypes.c_void_p)
        argtypes = kw.get("argtypes", ())
        proto = ctypes.CFUNCTYPE(restype, ctypes.c_void_p, ctypes.c_void_p, *argtypes)
        return proto(self._send)(obj, self._sel(name), *args)

    def _nsstr(self, s):
        return self._msg(self._cls("NSString"), "stringWithUTF8String:",
                         s.encode(), argtypes=(ctypes.c_char_p,))

    def _hold(self, obj):
        """autorelease 풀에 쓸려가지 않게 붙잡아 둔다 (Tk 이벤트 루프가 풀을 비운다)."""
        if obj:
            self._msg(obj, "retain")
            self._keep.append(obj)
        return obj

    # ── 색 큐브 만들기 ──────────────────────────────────────────────────
    def _cube_bytes(self, key_hex):
        """키 색은 투명, 그 언저리는 부드럽게 — 값은 알파를 곱한 상태로 넣는다.

        가장자리 픽셀은 캐릭터 색과 키 색이 섞인 값이라, 딱 잘라 지우면 키 색 테두리가
        남는다. 그래서 키에서 멀어질수록 알파를 올리면서 섞여 들어간 키 색 몫
        ((1-a)*K)을 빼 준다. 파츠 색은 키에서 충분히 떨어져 있어 영향이 없다.
        """
        import array
        n, rad, soft = self.N, self.RAD, self.SOFT
        key = key_hex.lstrip("#")
        rgb = tuple(int(key[i:i + 2], 16) for i in (0, 2, 4))
        ki = tuple(int(round(v / 255 * (n - 1))) for v in rgb)
        kf = tuple(v / 255.0 for v in rgb)
        step = 1.0 / (n - 1)
        buf = array.array("f", bytes(4 * 4 * n * n * n))
        rv = [i * step for i in range(n)]
        p = 0
        for bi in range(n):
            db = abs(bi - ki[2])
            bv = bi * step
            for gi in range(n):
                dgb = max(db, abs(gi - ki[1]))
                gv = gi * step
                row = []
                for ri in range(n):
                    d = max(dgb, abs(ri - ki[0]))
                    if d <= rad:                        # 키 색 → 완전 투명
                        row += (0.0, 0.0, 0.0, 0.0)
                    elif d >= soft:                     # 충분히 머니 손대지 않음
                        row += (rv[ri], gv, bv, 1.0)
                    else:                               # 중간 = 부드러운 경계
                        a = (d - rad) / float(soft - rad)
                        c = (rv[ri], gv, bv)
                        row += (min(max(c[0] - (1 - a) * kf[0], 0.0), a),
                                min(max(c[1] - (1 - a) * kf[1], 0.0), a),
                                min(max(c[2] - (1 - a) * kf[2], 0.0), a),
                                a)
                buf[p:p + 4 * n] = array.array("f", row)
                p += 4 * n
        return buf.tobytes(), ki

    def _build_filter(self, key_hex):
        raw, self.key_idx = self._cube_bytes(key_hex)
        data = self._hold(self._msg(
            self._cls("NSData"), "dataWithBytes:length:", raw, len(raw),
            argtypes=(ctypes.c_char_p, ctypes.c_ulong)))
        self._cg.CGColorSpaceCreateWithName.restype = ctypes.c_void_p
        self._cg.CGColorSpaceCreateWithName.argtypes = [ctypes.c_void_p]
        srgb = self._cg.CGColorSpaceCreateWithName(
            ctypes.c_void_p.in_dll(self._cg, "kCGColorSpaceSRGB"))
        # sRGB 로 못 박아야 큐브 격자와 캔버스 색이 어긋나지 않는다
        # (기본 작업 색공간은 선형이라 키 색이 다른 칸으로 밀린다).
        f = self._hold(self._msg(self._cls("CIFilter"), "filterWithName:",
                                 self._nsstr("CIColorCubeWithColorSpace"),
                                 argtypes=(ctypes.c_void_p,)))
        if not f:
            raise RuntimeError("CIColorCubeWithColorSpace 를 만들 수 없음")
        dim = self._msg(self._cls("NSNumber"), "numberWithInt:", self.N,
                        argtypes=(ctypes.c_int,))
        for val, key in ((dim, "inputCubeDimension"), (data, "inputCubeData"),
                         (srgb, "inputColorSpace")):
            self._msg(f, "setValue:forKey:", val, self._nsstr(key),
                      argtypes=(ctypes.c_void_p, ctypes.c_void_p))
        return f

    # ── 창에 걸기 ───────────────────────────────────────────────────────
    def windows(self):
        app = self._msg(self._cls("NSApplication"), "sharedApplication")
        arr = self._msg(app, "windows")
        n = self._msg(arr, "count", restype=ctypes.c_ulong)
        return [self._msg(arr, "objectAtIndex:", i, argtypes=(ctypes.c_ulong,))
                for i in range(n)]

    def apply_all(self):
        """이 앱의 모든 창에 필터를 건다.

        말풍선·할 일 패널은 나중에 생기므로 주기적으로 다시 부른다. 이미 걸린 창은
        건너뛰므로 반복 호출이 싸다. 키 색만 지우는 필터라 다른 창에 걸려도 무해하다.
        """
        if not self.filter:
            return 0
        done = 0
        for w in self.windows():
            try:
                cv = self._msg(w, "contentView")
                if not cv:
                    continue
                self._msg(cv, "setWantsLayer:", True, argtypes=(ctypes.c_bool,))
                lay = self._msg(cv, "layer")
                if not lay:
                    continue
                if self._msg(lay, "compositingFilter") == self.filter:
                    continue
                self._msg(lay, "setCompositingFilter:", self.filter,
                          argtypes=(ctypes.c_void_p,))
                done += 1
            except Exception:
                pass
        return done

    # ── 진단: 실제로 투명해졌는지 화면 합성 결과를 직접 읽는다 ──────────
    def probe(self, want_w, pts):
        """가로 폭이 want_w 인 창을 캡처해 지정 좌표의 ARGB 를 돌려준다.

        자기 앱 창만 찍으므로 화면 녹화 권한이 필요 없다. 알파가 0 이면 진짜 투명.
        """
        try:
            self._cg.CGWindowListCreateImage.restype = ctypes.c_void_p
            self._cg.CGWindowListCreateImage.argtypes = [
                _CGRect, ctypes.c_uint32, ctypes.c_uint32, ctypes.c_uint32]
            null = _CGRect(_CGPoint(float("inf"), float("inf")), _CGSize(0, 0))
            for w in self.windows():
                fr = self._msg(w, "frame", restype=_CGRect)
                if abs(fr.size.width - want_w) > 2:
                    continue
                wid = self._msg(w, "windowNumber", restype=ctypes.c_long)
                img = self._cg.CGWindowListCreateImage(
                    null, 1 << 3, ctypes.c_uint32(wid), 1)
                if not img:
                    return None
                rep = self._msg(self._msg(self._cls("NSBitmapImageRep"), "alloc"),
                                "initWithCGImage:", img, argtypes=(ctypes.c_void_p,))
                data = self._msg(rep, "bitmapData")
                if not data:
                    return None
                pw = self._msg(rep, "pixelsWide", restype=ctypes.c_long)
                ph = self._msg(rep, "pixelsHigh", restype=ctypes.c_long)
                row = self._msg(rep, "bytesPerRow", restype=ctypes.c_long)
                spp = self._msg(rep, "samplesPerPixel", restype=ctypes.c_long)
                buf = ctypes.string_at(data, row * ph)
                sx = pw / float(fr.size.width)      # 레티나면 2
                out = []
                for (x, y) in pts:
                    px, py = int(x * sx), int(y * sx)
                    if not (0 <= px < pw and 0 <= py < ph):
                        out.append(None)
                        continue
                    o = py * row + px * spp
                    out.append(tuple(buf[o + i] for i in range(spp)))
                return {"scale": sx, "px": out}
        except Exception as e:
            self.err = repr(e)
        return None


class _CGPoint(ctypes.Structure):
    _fields_ = [("x", ctypes.c_double), ("y", ctypes.c_double)]


class _CGSize(ctypes.Structure):
    _fields_ = [("width", ctypes.c_double), ("height", ctypes.c_double)]


class _CGRect(ctypes.Structure):
    _fields_ = [("origin", _CGPoint), ("size", _CGSize)]


if getattr(sys, "frozen", False) and not os.path.exists(os.path.abspath(__file__)):
    # PyInstaller 번들 내부에서 임포트된 경우 (자동 업데이트로 받은 파일이면
    # __file__이 실제 디스크에 존재하므로 그 폴더를 기준으로 삼는다)
    HERE = sys._MEIPASS
else:
    HERE = os.path.dirname(os.path.abspath(__file__))
TRANSPARENT = "#010203"          # 투명 키 색

# 맥 전용 투명 키 색. 윈도우는 창 관리자가 색상키를 처리해 주지만 맥에는 그게 없어서
# CoreImage 로 직접 뺀다(_MacChromaKey). 파츠 이미지와 UI 팔레트 어디에도 없는 색을
# 골라야 캐릭터에 구멍이 뚫리지 않는다. 이 색은 파츠 전체를 훑어 고른 값으로,
# 팔레트에서 가장 가까운 색과도 색 큐브 기준 12칸 떨어져 있다.
# (윈도우용 #010203 을 쓸 수 없는 이유: 파츠가 순검정 외곽선을 대량으로 써서
#  검정 근처를 키로 잡으면 눈·외곽선이 함께 지워진다.)
MAC_KEY = "#5d0051"

KEY_ROT = (-7.0, 7.0)            # 타이핑 시 손 회전(어깨 축) 범위 (도)
PEN_KB_ROT = (-6.0, 6.0)
SHADOW_PAD = 16                  # 그림자 이미지 여백 (가장자리 파츠 잘림 방지)
TIMER_H = 92                     # 타이머 카드 영역 높이 (게이지형 = 준사)
OY_CLOCK_COMPACT = 70            # 시계형 카드 접힘 (상태+시간 한 줄)
OY_CLOCK_OPEN = 182             # 시계형 카드 펼침 (시계 + 시간)

# 타이머 카드 팔레트 (준사 배색)
CARD_BORDER = "#f2b8c6"          # 소프트 핑크
CARD_NAVY = "#3a4a6b"
CARD_GRAY = "#9aa7bd"
CARD_TRACK = "#eef0f5"
CARD_FILL = "#f2a7b3"
DOT_ON, DOT_OFF = "#7ccf8f", "#cfcfcf"

# 환경설정 기본값 (캐릭터 폴더의 .settings.json에 저장)
DEFAULT_SETTINGS = {
    "goal_hours": 6.0,    # 목표 작업시간
    "idle_sec": 15.0,     # 휴식 전환(초)
    "show_timer": None,   # None = config 기본값 따름
    "trail": False,       # 타블렛 낙서 표시
    "topmost": True,      # 항상 위
    "stretch_hint": 3,    # 스트레칭 알림에 '눌러 주세요' 안내를 붙일 남은 횟수
    "day_start": 6,       # 하루가 바뀌는 시각 (0이면 달력 날짜 그대로)
    "stretch_every": "20분마다",   # 스트레칭 알림 간격 ("끄기"면 안 뜸)
    "pen_monitor": "자동", # 펜을 따라갈 화면 (자동 = 커서가 있는 화면)
    "scale_pct": 100,     # 캐릭터 크기(%)
    "font_pct": 100,      # 타이머·말풍선 글자 크기(%)
    "work_apps_only": True,   # 작업 프로그램이 앞에 있을 때만 시간 측정
    "work_apps": "clipstudiopaint.exe, photoshop.exe, sai2.exe, krita.exe",
    "sleep_min": 10,      # 이 시간(분) 동안 무입력이면 수면 모드
    "shadow": True,       # 캐릭터 뒤 옅은 그림자
    "clock_open": False,  # 시계형 카드에서 시계 펼침 상태
    "autostart": True,    # 윈도우 시작 시 자동 실행 (exe로 배포된 경우만 적용)
    "sound": True,        # 타자 소리 (Mechvibes 팩)
    "sound_volume": 60,   # 타자 소리 볼륨 (0~100)
    "pen_volume": 10,     # 펜 긋는 소리 볼륨 (0~100)
    "poke_volume": 40,    # 캐릭터를 눌렀을 때 나는 소리 볼륨 (0~100)
    "sound_pack": "banana split lubed",
    "skin": "기본",        # 패션 슬롯 이름
}
DOT_OTHER = "#f0b95e"     # 딴짓 중(작업앱 아님) 표시색


class _POINT(ctypes.Structure):
    _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]


class _RECT(ctypes.Structure):
    _fields_ = [("left", ctypes.c_long), ("top", ctypes.c_long),
                ("right", ctypes.c_long), ("bottom", ctypes.c_long)]


class _MONITORINFO(ctypes.Structure):
    _fields_ = [("cbSize", ctypes.c_ulong), ("rcMonitor", _RECT),
                ("rcWork", _RECT), ("dwFlags", ctypes.c_ulong)]


class _LASTINPUTINFO(ctypes.Structure):
    _fields_ = [("cbSize", ctypes.c_uint), ("dwTime", ctypes.c_uint)]


class _SIZE(ctypes.Structure):
    _fields_ = [("cx", ctypes.c_long), ("cy", ctypes.c_long)]


class _BLENDFUNCTION(ctypes.Structure):
    _fields_ = [("BlendOp", ctypes.c_byte), ("BlendFlags", ctypes.c_byte),
                ("SourceConstantAlpha", ctypes.c_byte), ("AlphaFormat", ctypes.c_byte)]


class _BITMAPINFOHEADER(ctypes.Structure):
    _fields_ = [("biSize", ctypes.c_uint32), ("biWidth", ctypes.c_long),
                ("biHeight", ctypes.c_long), ("biPlanes", ctypes.c_uint16),
                ("biBitCount", ctypes.c_uint16), ("biCompression", ctypes.c_uint32),
                ("biSizeImage", ctypes.c_uint32), ("biXPelsPerMeter", ctypes.c_long),
                ("biYPelsPerMeter", ctypes.c_long), ("biClrUsed", ctypes.c_uint32),
                ("biClrImportant", ctypes.c_uint32)]


class ShadowLayer:
    """캐릭터 창 뒤에 깔리는 진짜 반투명 그림자 (per-pixel alpha 레이어 창).

    색상키 투명창은 반투명을 표현할 수 없으므로, 그림자만 별도의
    UpdateLayeredWindow 창으로 그린다. 클릭은 통과(WS_EX_TRANSPARENT).
    """

    def __init__(self, root, image, offset=(7, 9)):
        self.offset = offset
        self.top = tk.Toplevel(root)
        self.top.overrideredirect(True)
        self.top.attributes("-topmost", True)
        self.top.update_idletasks()
        self.hwnd = int(self.top.wm_frame(), 16)
        u = ctypes.windll.user32
        GWL_EXSTYLE = -20
        ex = u.GetWindowLongW(self.hwnd, GWL_EXSTYLE)
        # LAYERED | TRANSPARENT(클릭 통과) | TOOLWINDOW | NOACTIVATE
        u.SetWindowLongW(self.hwnd, GWL_EXSTYLE,
                         ex | 0x80000 | 0x20 | 0x80 | 0x8000000)
        self._push(image)

    def _push(self, im):
        """BGRA 비트맵을 레이어 창에 업로드 (그림자는 검정이라 premultiply 불요)."""
        u, g = ctypes.windll.user32, ctypes.windll.gdi32
        w, h = im.size
        data = im.tobytes("raw", "BGRA")
        hdc = u.GetDC(0)
        mem = g.CreateCompatibleDC(hdc)
        bmi = _BITMAPINFOHEADER()
        bmi.biSize = ctypes.sizeof(_BITMAPINFOHEADER)
        bmi.biWidth, bmi.biHeight = w, -h
        bmi.biPlanes, bmi.biBitCount = 1, 32
        bits = ctypes.c_void_p()
        hbm = g.CreateDIBSection(hdc, ctypes.byref(bmi), 0,
                                 ctypes.byref(bits), None, 0)
        ctypes.memmove(bits, data, len(data))
        old = g.SelectObject(mem, hbm)
        blend = _BLENDFUNCTION(0, 0, 255, 1)  # AC_SRC_OVER, alpha 채널 사용
        # 세 번째 인자는 '창을 옮길 새 화면 좌표'다. (0,0)을 넘기면 이미지를
        # 바꿀 때마다 그림자 창이 화면 좌상단으로 튀어 사라진 것처럼 보인다.
        # 위치를 바꿀 생각이 없으므로 NULL을 넘겨 그대로 둔다.
        u.UpdateLayeredWindow(self.hwnd, hdc, None,
                              ctypes.byref(_SIZE(w, h)), mem,
                              ctypes.byref(_POINT(0, 0)), 0,
                              ctypes.byref(blend), 2)  # ULW_ALPHA
        g.SelectObject(mem, old)
        g.DeleteObject(hbm)
        g.DeleteDC(mem)
        u.ReleaseDC(0, hdc)

    def set_image(self, image):
        """그림자 이미지 교체 (시계 토글로 크기가 바뀔 때)."""
        self._push(image)

    def place(self, x, y, owner_hwnd):
        """본체 창 바로 아래 z순서로, 오프셋만큼 밀린 위치에 배치."""
        SWP_NOSIZE, SWP_NOACTIVATE = 0x1, 0x10
        ctypes.windll.user32.SetWindowPos(
            self.hwnd, owner_hwnd, x + self.offset[0], y + self.offset[1],
            0, 0, SWP_NOSIZE | SWP_NOACTIVATE)


class _WAVEFORMATEX(ctypes.Structure):
    _fields_ = [("wFormatTag", ctypes.c_uint16), ("nChannels", ctypes.c_uint16),
                ("nSamplesPerSec", ctypes.c_uint32), ("nAvgBytesPerSec", ctypes.c_uint32),
                ("nBlockAlign", ctypes.c_uint16), ("wBitsPerSample", ctypes.c_uint16),
                ("cbSize", ctypes.c_uint16)]


class _WAVEHDR(ctypes.Structure):
    _fields_ = [("lpData", ctypes.c_void_p), ("dwBufferLength", ctypes.c_uint32),
                ("dwBytesRecorded", ctypes.c_uint32), ("dwUser", ctypes.c_void_p),
                ("dwFlags", ctypes.c_uint32), ("dwLoops", ctypes.c_uint32),
                ("lpNext", ctypes.c_void_p), ("reserved", ctypes.c_void_p)]


# 샘플 폭(바이트)별 정수 타입 — 볼륨을 샘플에 곱할 때 사용
_SAMPLE_CTYPE = {1: ctypes.c_int8, 2: ctypes.c_int16, 4: ctypes.c_int32}


def _scaled_buffer(data, gain, sampwidth):
    """PCM 바이트에 gain을 곱한 재생 버퍼. 비트 심도(16/32bit)에 맞춰 스케일.

    waveOutSetVolume이 드라이버에 무시될 수 있어 샘플 값 자체를 조절한다.
    """
    buf = ctypes.create_string_buffer(data, len(data))
    ct = _SAMPLE_CTYPE.get(sampwidth)
    if gain < 0.999 and ct is not None and len(data) >= sampwidth:
        n = len(data) // sampwidth
        arr = (ct * n).from_buffer(buf)
        for i in range(n):
            arr[i] = int(arr[i] * gain)
    return buf


class SoundPack:
    """Mechvibes 사운드 팩(multi 타입: 키별 wav) 재생기.

    winmm waveOut API 직접 호출 — 외부 라이브러리 불필요, 어느 스레드에서든
    안전(메시지 펌프 불요), 재생마다 독립 장치라 동시 재생 가능.
    (MCI는 연 스레드에 묶여 리스너 스레드에서 멈추는 문제가 있어 사용 안 함)
    """

    def __init__(self, folder, volume=60):
        import threading
        import wave
        with open(os.path.join(folder, "config.json"), encoding="utf-8") as fp:
            cfg = json.load(fp)
        if cfg.get("key_define_type", "multi") != "multi":
            raise ValueError("single 타입 팩 미지원 — wav 분할형 팩을 사용하세요")
        names = []
        for v in cfg.get("defines", {}).values():
            if isinstance(v, str) and v and v not in names:
                names.append(v)
        self.raw = []             # (WAVEFORMATEX, 원본PCM, 샘플폭)
        slot = {}                 # 파일 이름 -> raw 안에서의 번호
        for name in names:
            path = os.path.join(folder, name)
            if not (name.lower().endswith(".wav") and os.path.exists(path)):
                continue
            with wave.open(path, "rb") as w:
                ch, sw, fr = w.getnchannels(), w.getsampwidth(), w.getframerate()
                data = w.readframes(w.getnframes())
            wfx = _WAVEFORMATEX(1, ch, fr, fr * ch * sw, ch * sw, sw * 8, 0)
            slot[name] = len(self.raw)
            self.raw.append((wfx, data, sw))
        if not self.raw:
            raise ValueError("재생 가능한 wav가 없음")
        # 팩은 스캔코드마다 쓸 음원을 config.json에 적어 둔다. 스페이스·백스페이스
        # 처럼 소리가 다른 키를 위한 것인데, 지금까지는 이 표를 버리고 아무 음원이나
        # 골라 썼다 (스페이스 소리가 엉뚱한 글자 키에서 났다).
        self.by_code = {}
        for code, fname in (cfg.get("defines") or {}).items():
            i = slot.get(fname)
            if i is not None:
                self.by_code[str(code)] = i
        self._active = []         # (핸들, WAVEHDR) — 재생 끝나면 정리
        self._lock = threading.Lock()
        self.set_volume(volume)

    def set_volume(self, volume):
        """볼륨(0~100)을 샘플에 곱해 재생용 버퍼 준비 (드라이버 볼륨 무시 대비)."""
        self.volume = max(0.0, min(float(volume), 100.0))
        gain = self.volume / 100.0
        self.sounds = []          # (WAVEFORMATEX, 버퍼, 길이)
        if gain <= 0.0:
            return
        for wfx, data, sw in self.raw:
            self.sounds.append((wfx, _scaled_buffer(data, gain, sw), len(data)))

    def play(self, key, code=None):
        if not self.sounds:
            return
        i = self.by_code.get(str(code)) if code is not None else None
        if i is None or i >= len(self.sounds):
            i = hash(str(key)) % len(self.sounds)   # 표에 없는 키는 아무거나
        wfx, buf, ln = self.sounds[i]
        wm = ctypes.windll.winmm
        h = ctypes.c_void_p()
        if wm.waveOutOpen(ctypes.byref(h), 0xFFFFFFFF, ctypes.byref(wfx), 0, 0, 0):
            return
        wm.waveOutSetVolume(h, 0xFFFFFFFF)   # 앱/장치 볼륨 고정 해제 (실볼륨은 샘플로)
        hdr = _WAVEHDR()
        hdr.lpData = ctypes.cast(buf, ctypes.c_void_p)
        hdr.dwBufferLength = ln
        wm.waveOutPrepareHeader(h, ctypes.byref(hdr), ctypes.sizeof(_WAVEHDR))
        wm.waveOutWrite(h, ctypes.byref(hdr), ctypes.sizeof(_WAVEHDR))
        with self._lock:
            self._active.append((h, hdr))
            self._reap_locked(limit=24)

    def reap(self):
        """재생이 끝난 장치 정리 (주기 호출용)."""
        with self._lock:
            self._reap_locked(limit=24)

    def _reap_locked(self, limit):
        wm = ctypes.windll.winmm
        keep = []
        for h, hdr in self._active:
            if hdr.dwFlags & 0x1:     # WHDR_DONE
                wm.waveOutUnprepareHeader(h, ctypes.byref(hdr),
                                          ctypes.sizeof(_WAVEHDR))
                wm.waveOutClose(h)
            else:
                keep.append((h, hdr))
        while len(keep) > limit:      # 안전판: 과도한 동시 재생 방지
            h, hdr = keep.pop(0)
            wm.waveOutReset(h)
            wm.waveOutUnprepareHeader(h, ctypes.byref(hdr),
                                      ctypes.sizeof(_WAVEHDR))
            wm.waveOutClose(h)
        self._active = keep

    def close(self):
        with self._lock:
            wm = ctypes.windll.winmm
            for h, hdr in self._active:
                wm.waveOutReset(h)
                wm.waveOutUnprepareHeader(h, ctypes.byref(hdr),
                                          ctypes.sizeof(_WAVEHDR))
                wm.waveOutClose(h)
            self._active = []


class PenSound:
    """선을 긋기 시작할 때 스크리블 클립 하나를 랜덤 재생 (한 번 '슥').

    짧은 선이든 긴 선이든 스트로크마다 클립 하나. 지속음(bed) 없음.
    볼륨은 waveOutSetVolume이 드라이버에 무시될 수 있어(장치별 볼륨 미지원)
    샘플 값 자체에 곱해 확실히 적용한다. 0이면 아예 재생하지 않는다.
    """

    def __init__(self, folder, volume=35):
        import wave
        self.raw = []             # (WAVEFORMATEX, 원본PCM, 샘플폭)
        names = [f for f in sorted(os.listdir(folder)) if f.lower().endswith(".wav")]
        clips = [f for f in names if f.lower().startswith("clip")] or names
        for f in clips:
            with wave.open(os.path.join(folder, f), "rb") as w:
                ch, sw, fr = w.getnchannels(), w.getsampwidth(), w.getframerate()
                data = w.readframes(w.getnframes())
            wfx = _WAVEFORMATEX(1, ch, fr, fr * ch * sw, ch * sw, sw * 8, 0)
            self.raw.append((wfx, data, sw))
        if not self.raw:
            raise ValueError("펜 소리 wav 없음")
        self.set_volume(volume)
        self._cur = None          # (핸들, WAVEHDR, 버퍼)

    def set_volume(self, volume):
        """볼륨(0~100)을 샘플에 곱해 재생용 버퍼를 준비."""
        self.volume = max(0.0, min(float(volume), 100.0))
        gain = self.volume / 100.0
        self.clips = []           # (WAVEFORMATEX, 버퍼, 길이)
        if gain <= 0.0:
            return                # 무음이면 버퍼 안 만듦 → play()가 그냥 반환
        for wfx, data, sw in self.raw:
            self.clips.append((wfx, _scaled_buffer(data, gain, sw), len(data)))

    def play(self):
        """랜덤 클립 하나 재생 (선 긋기 시작 시). 볼륨 0이면 무음."""
        if not self.clips:
            return
        wm = ctypes.windll.winmm
        if self._cur is not None:
            self._release(self._cur)
            self._cur = None
        wfx, buf, ln = random.choice(self.clips)
        h = ctypes.c_void_p()
        if wm.waveOutOpen(ctypes.byref(h), 0xFFFFFFFF, ctypes.byref(wfx), 0, 0, 0):
            return
        wm.waveOutSetVolume(h, 0xFFFFFFFF)   # 앱/장치 볼륨 고정 해제 (실볼륨은 샘플로)
        hdr = _WAVEHDR()
        hdr.lpData = ctypes.cast(buf, ctypes.c_void_p)
        hdr.dwBufferLength = ln
        wm.waveOutPrepareHeader(h, ctypes.byref(hdr), ctypes.sizeof(_WAVEHDR))
        wm.waveOutWrite(h, ctypes.byref(hdr), ctypes.sizeof(_WAVEHDR))
        self._cur = (h, hdr, buf)

    def stop(self):
        if self._cur is not None:
            self._release(self._cur)
            self._cur = None

    @staticmethod
    def _release(dev):
        wm = ctypes.windll.winmm
        h, hdr, _buf = dev
        wm.waveOutReset(h)
        wm.waveOutUnprepareHeader(h, ctypes.byref(hdr), ctypes.sizeof(_WAVEHDR))
        wm.waveOutClose(h)


class PenGrainSound:
    """펜 긋는 소리 — 지속 재생(연속 스크레이프) 방식.

    긴 스크레이프 녹음(sustain.wav)이 있으면 그중 가장 고른 구간을 골라
    이음매 없이 무한 반복한다(실제 연필 질감 그대로). 없으면 짧은 클립들을
    진폭 평탄화해 만든 베드로 폴백한다.
      · 짧은 획은 짧게, 긴 획은 길게 — 소리 길이가 손을 그대로 따라간다.
      · 한 획이 '스으으윽' 하나로 이어진다(루프가 매끄러워 회전음 없음).
      · 획마다 피치만 살짝 달리해 반복감을 줄이고, 시작 볼륨에 속도를 싣는다.

    **페이드는 전부 샘플에 미리 구워 둔다.** 재생 중 waveOutSetVolume으로
    줄이면 드라이버에 따라 볼륨이 핸들별이 아니라 전역으로 먹어서, 직전 획의
    페이드아웃이 방금 시작한 다음 획까지 끌어내린다(빠른 연타에서 소리가
    10%대로 씹히던 원인). 그래서 짧은 클립은 꼬리를 구워 두고 발사 후엔
    손대지 않고, 루프는 페이드인 머리·페이드아웃 꼬리 버퍼를 따로 재생한다.
    """

    BED_S = 1.5            # 베드 최대 길이(초) — 길수록 반복 주기가 길어짐
    XFADE_S = 0.04         # 이음매 크로스페이드(초)
    HEAD_S = 0.12          # 루프 페이드인 머리(초) — 짧은 클립 밑에서 올라옴
    TAIL_S = 0.13          # 루프 페이드아웃 꼬리(초)
    SHORT_CAP = 0.26       # 짧은 클립 최대 길이(초) — 획보다 길게 남지 않게
    SHORT_MAX = 0.16       # 이 시간 넘게 이어지면 루프로 전환(짧은 클립과 겹침)
    MOVE_MIN = 4.0         # 획 시작 판정(px) — 마우스 이벤트로 재므로 낮게 잡는다

    def __init__(self, folder, volume=30):
        import wave
        names = [f for f in sorted(os.listdir(folder)) if f.lower().endswith(".wav")]
        longs = [f for f in names if "sustain" in f.lower() or "long" in f.lower()]
        self.fr = 44100

        def read(fname):
            with wave.open(os.path.join(folder, fname), "rb") as w:
                if w.getsampwidth() != 2 or w.getnchannels() != 1:
                    raise ValueError("펜 소리는 16bit 모노 wav만 지원")
                self.fr = w.getframerate()
                return list(memoryview(bytearray(w.readframes(w.getnframes()))).cast("h"))

        if longs:                                     # 실제 긴 스크레이프 → 그대로 루프
            flat = self._steady_bed(read(longs[0]))
        else:                                         # 짧은 클립 → 평탄화 베드(폴백)
            pcm = []
            for f in ([c for c in names if c.lower().startswith("clip")] or names):
                pcm += read(f)
            flat = self._voiced_flat(pcm)
        m = len(flat)
        X = max(4, int(self.fr * self.XFADE_S))
        Lb = min(m - X, int(self.fr * self.BED_S))
        if Lb < 8:
            raise ValueError("펜 소리가 너무 짧아 베드를 못 만듦")
        # 크로스페이드 루프: loop[Lb-1] → loop[0] 이 매끄럽게 맞물리게
        loop = (ctypes.c_int16 * Lb)()
        for i in range(Lb):
            if i < X:
                w = i / X
                loop[i] = int(flat[i] * w + flat[Lb + i] * (1.0 - w))
            else:
                loop[i] = flat[i]
        self.loop_pcm = bytes(loop)
        # 루프 머리(페이드인)·꼬리(페이드아웃) — 볼륨 API 대신 이걸 재생한다.
        H = min(Lb, max(8, int(self.fr * self.HEAD_S)))
        head = (ctypes.c_int16 * H)()
        for i in range(H):
            head[i] = int(loop[i] * (i / H))
        self._head_pcm = bytes(head)
        T = min(Lb, max(8, int(self.fr * self.TAIL_S)))
        rise = max(2, int(self.fr * 0.003))       # 이음매 클릭 방지용 3ms 상승
        tail = (ctypes.c_int16 * T)()
        for i in range(T):
            g = (1.0 - i / T) * (min(i, rise) / rise)
            tail[i] = int(loop[i] * g)
        self._tail_pcm = bytes(tail)
        # 짧은 획용: clip_*.wav 를 원샷 재생. 길이를 SHORT_CAP으로 자르고 끝에
        # 페이드 꼬리를 구워 둔다 — 재생 뒤엔 손대지 않아도 획 길이에 맞는다.
        self.shorts = []
        for f in [c for c in names if c.lower().startswith("clip")]:
            with wave.open(os.path.join(folder, f), "rb") as w:
                if w.getsampwidth() != 2 or w.getnchannels() != 1:
                    continue
                s = list(memoryview(bytearray(
                    w.readframes(w.getnframes()))).cast("h"))
            cap = int(self.fr * self.SHORT_CAP)
            if len(s) > cap:
                s = s[:cap]
            fo = max(4, int(self.fr * 0.05))      # 끝 50ms 페이드아웃
            if len(s) > fo:
                for i in range(fo):
                    s[len(s) - fo + i] = int(s[len(s) - fo + i] * (1.0 - i / fo))
            arr = (ctypes.c_int16 * len(s))(*s)
            self.shorts.append(bytes(arr))
        self.shorts.sort(key=len)
        # 마우스 콜백(후킹 스레드)과 그리기 루프(메인)가 같이 보는 것들을 지킨다
        self._lock = threading.Lock()
        self._short_bufs = []            # [클립][볼륨단계] 미리 구운 재생 버퍼
        self._tail_bufs = {}             # 볼륨별 루프 꼬리 버퍼
        self.set_volume(volume)
        self._voice = None               # 루프 재생 (handle, WAVEHDR, buf)
        self._playing = False            # 루프 재생 중인가
        self._down = False               # 펜이 눌려 있는가 (마우스 콜백이 갱신)
        self._stroke_dist = 0.0          # 이번 획에서 누적 이동(px)
        self._stroke_fired = False       # 이번 획에서 짧은 소리를 냈는가
        self._stroke_t = 0.0             # 짧은 소리를 낸 시각(루프 전환 기준)
        self._moving_t = 0.0             # 마지막으로 실제 움직인 시각
        self._cur_speed = 0.0            # 최근 이동 속도(클립 선택·볼륨용)
        self._last_xy = None             # 직전 마우스 이벤트 좌표
        self._last_ev = 0.0              # 직전 마우스 이벤트 시각
        self._last_pick = -1             # 직전에 고른 클립 (연속 반복 방지)
        self._oneshots = []              # 재생 중인 원샷들 [(h, hdr, buf)]
        self._loop_bufs = {}             # 볼륨별 루프 버퍼 캐시 (매번 만들면 느리다)
        self._loop_gain = 0.5            # 현재 루프의 볼륨 (꼬리를 같은 크기로)
        self._loop_fr = self.fr          # 현재 루프의 재생 주파수 (꼬리도 같게)

    def _win_rms(self, src, win):
        return [(sum(src[i + j] * src[i + j] for j in range(win)) / win) ** 0.5
                for i in range(0, len(src) - win, win)]

    def _steady_bed(self, src):
        """긴 녹음에서 가장 고른 구간을 골라 큰 기복만 살짝 다듬는다.
        실제 스크레이프 질감은 최대한 남긴다(평탄화 약하게)."""
        fr = self.fr
        win = max(8, int(fr * 0.02))
        need = min(len(src) - 1, int(fr * self.BED_S) + int(fr * self.XFADE_S))
        rms = self._win_rms(src, win)
        wc = max(1, need // win)
        best = (1e18, 0)
        for s in range(0, max(1, len(rms) - wc)):     # RMS 변동이 가장 작은 창
            seg = rms[s:s + wc]
            mean = sum(seg) / len(seg)
            var = sum((r - mean) ** 2 for r in seg) / len(seg)
            cv = var ** 0.5 / (mean + 1e-9)
            if cv < best[0]:
                best = (cv, s * win)
        s0 = best[1]
        seg = src[s0:s0 + need]
        peak = max(1.0, max(abs(v) for v in seg))
        target, floor = 0.6 * peak, 0.45 * peak       # 약한 평탄화(±완만)
        out = []
        for i in range(0, len(seg) - win + 1, win):
            w2 = seg[i:i + win]
            r = (sum(v * v for v in w2) / win) ** 0.5
            g = min(1.8, target / max(r, floor))
            out.extend(max(-32767, min(32767, int(v * g))) for v in w2)
        return out

    def _voiced_flat(self, src):
        """짧은 클립용 폴백 — 소리 나는 창만 모아 강하게 평탄화한다."""
        win = max(8, int(self.fr * 0.012))
        rms = [(i, r) for i, r in
               zip(range(0, len(src) - win, win), self._win_rms(src, win))]
        if not rms:
            raise ValueError("펜 소리가 너무 짧음")
        peak = max(r for _, r in rms) or 1.0
        thr = 0.25
        voiced = [i for i, r in rms if r >= thr * peak]
        while len(voiced) * win < self.fr * 0.25 and thr > 0.05:
            thr -= 0.05
            voiced = [i for i, r in rms if r >= thr * peak]
        target, floor = 0.5 * peak, 0.30 * peak
        out = []
        for i in voiced:
            seg = src[i:i + win]
            r = (sum(v * v for v in seg) / win) ** 0.5
            g = target / max(r, floor)
            out.extend(max(-32767, min(32767, int(v * g))) for v in seg)
        return out

    GAIN_LEVELS = 3        # 속도별 볼륨 단계 (미리 구워 두는 가짓수)

    def set_volume(self, volume):
        """볼륨을 바꾸고, 짧은 클립 재생용 버퍼를 미리 구워 둔다.

        재생 시점(마우스 콜백)에 샘플마다 볼륨을 곱하면 후킹 스레드에서
        1만 번짜리 반복이 돌아 입력이 밀린다. 미리 만들어 두고 고르기만 한다.
        """
        self.volume = max(0.0, min(float(volume), 100.0))
        base = self.volume / 100.0
        self._short_bufs = []
        self._tail_bufs = {}
        if base <= 0.0:
            return
        for pcm in self.shorts:
            row = []
            for lv in range(self.GAIN_LEVELS):
                g = base * (0.7 + 0.3 * (lv / max(1, self.GAIN_LEVELS - 1)))
                row.append(_scaled_buffer(pcm, g, 2))
            self._short_bufs.append(row)

    def _tail_buf(self, gain):
        """루프 꼬리 버퍼 (볼륨별 캐시). 메인 스레드에서만 만든다."""
        key = round(gain, 2)
        buf = self._tail_bufs.get(key)
        if buf is None:
            if len(self._tail_bufs) > 8:
                self._tail_bufs.clear()
            buf = _scaled_buffer(self._tail_pcm, key, 2)
            self._tail_bufs[key] = buf
        return buf

    # ── 마우스 콜백에서 즉시 호출 (그리기 루프를 기다리지 않는다) ──────────
    # 펜 소리가 그리기 루프에 묶여 있으면 프레임 간격(33~66ms)만큼 늦게 난다.
    # 타자 소리처럼 입력 이벤트에서 바로 재생해야 '댄 순간' 느낌이 난다.

    def pen_down(self, x, y, now):
        """펜을 댄 순간 — 새 획 시작 (소리는 아직, 움직임을 봐야 탭과 구분된다)."""
        self._down = True
        self._stroke_dist = 0.0
        self._stroke_fired = False
        self._last_xy = (x, y)
        self._last_ev = now

    def pen_move(self, x, y, now):
        """마우스가 움직일 때마다 — MOVE_MIN을 넘는 즉시 짧은 클립을 낸다."""
        if self._last_xy is not None:
            d = math.hypot(x - self._last_xy[0], y - self._last_xy[1])
            dt = now - self._last_ev
            if 0 < dt < 0.5:
                sp = d / dt
                self._cur_speed += (sp - self._cur_speed) * 0.5   # 살짝 평활
            if d > 0.5:
                self._moving_t = now
            if self._down:
                self._stroke_dist += d
                if not self._stroke_fired and self._stroke_dist >= self.MOVE_MIN:
                    self._stroke_fired = True
                    self._stroke_t = now
                    if self.volume > 0.0:
                        self._play_short(self._cur_speed)
        self._last_xy = (x, y)
        self._last_ev = now

    def pen_up(self, now):
        """펜을 뗀 순간 — 표시만 남기고, 루프 정지는 tick(메인 스레드)에 맡긴다.

        여기서 직접 장치를 닫으면 같은 프레임에 tick도 닫으려 들어 같은
        핸들을 두 번 닫는다(access violation → 팔 구역 차단·입력 지연 사고).
        소리 장치를 여닫는 일은 메인 스레드만 하도록 못 박는다.
        """
        self._down = False
        self._stroke_fired = False

    # ── 그리기 루프에서 호출 (루프 전환·정리) ──────────────────────────────

    def tick(self, now, enabled=True):
        """프레임마다 호출 — 끝난 소리를 거두고 긴 획이면 루프로 넘어간다."""
        self._reap()
        want = (enabled and self._down and self._stroke_fired
                and now - self._moving_t < 0.18
                and now - self._stroke_t > self.SHORT_MAX)
        if want and not self._playing and self.volume > 0.0:
            self._start()
        elif self._playing and not want:
            self._stop_loop(tail=True)

    def _pick_short(self, speed):
        """속도에 맞는 클립 고르기 — 빠르면 짧고 경쾌한 것, 느리면 긴 것.
        (shorts는 길이순 정렬) 직전과 같은 것은 피해 반복감을 줄인다."""
        n = len(self.shorts)
        half = max(1, n // 2)
        pool = range(0, half) if speed >= 350.0 else range(n - half, n)
        cand = [i for i in pool if i != self._last_pick] or list(pool)
        i = random.choice(cand)
        self._last_pick = i
        return i

    def _oneshot(self, buf, nbytes, fr2):
        """이미 볼륨이 반영된 버퍼를 독립 장치로 재생한다.

        마우스 콜백(후킹 스레드)에서도 불리므로 무거운 계산을 하지 않는다 —
        볼륨 곱하기는 set_volume에서 미리 구워 둔다. 후킹 스레드가 늦어지면
        윈도우가 시스템 전체의 펜/마우스 이벤트를 지연시켜, 그림 선이
        직선으로 이어지고 타자가 굼떠지는 사고가 난다.
        """
        wfx = _WAVEFORMATEX(1, 1, fr2, fr2 * 2, 2, 16, 0)
        wm = ctypes.windll.winmm
        h = ctypes.c_void_p()
        if wm.waveOutOpen(ctypes.byref(h), 0xFFFFFFFF, ctypes.byref(wfx), 0, 0, 0):
            return
        wm.waveOutSetVolume(h, 0xFFFFFFFF)   # 장치 볼륨은 만땅 고정 — 이후 안 건드린다
        hdr = _WAVEHDR()
        hdr.lpData = ctypes.cast(buf, ctypes.c_void_p)
        hdr.dwBufferLength = nbytes
        wm.waveOutPrepareHeader(h, ctypes.byref(hdr), ctypes.sizeof(_WAVEHDR))
        wm.waveOutWrite(h, ctypes.byref(hdr), ctypes.sizeof(_WAVEHDR))
        with self._lock:                     # 회수 목록은 메인 스레드와 공유
            self._oneshots.append((h, hdr, buf))

    def _play_short(self, speed):
        """짧은 클립 하나를 즉시 재생 (미리 구워 둔 버퍼를 고르기만 한다)."""
        if not self._short_bufs:
            return
        i = self._pick_short(speed)
        g = max(0.0, min(1.0, (speed - 30.0) / 500.0))
        lv = min(self.GAIN_LEVELS - 1, int(g * self.GAIN_LEVELS))
        fr2 = max(8000, int(self.fr * random.uniform(0.97, 1.06)))
        self._oneshot(self._short_bufs[i][lv], len(self.shorts[i]), fr2)

    def _reap(self):
        """끝난 원샷(짧은 클립·루프 꼬리)을 회수한다 (메인 스레드 전용)."""
        with self._lock:
            if not self._oneshots:
                return
            pending, self._oneshots = self._oneshots, []
        wm = ctypes.windll.winmm
        keep = []
        for h, hdr, buf in pending:
            if hdr.dwFlags & 0x00000001:        # WHDR_DONE
                wm.waveOutUnprepareHeader(h, ctypes.byref(hdr), ctypes.sizeof(_WAVEHDR))
                wm.waveOutClose(h)
            else:
                keep.append((h, hdr, buf))
        with self._lock:                        # 회수 중 새로 들어온 것과 합친다
            self._oneshots = keep + self._oneshots

    def _loop_buf(self, gain):
        """볼륨별 루프 본체 버퍼 (1.5초짜리라 매번 만들면 프레임을 잡아먹는다)."""
        key = round(gain, 2)
        buf = self._loop_bufs.get(key)
        if buf is None:
            if len(self._loop_bufs) > 8:
                self._loop_bufs.clear()
            buf = _scaled_buffer(self.loop_pcm, key, 2)
            self._loop_bufs[key] = buf
        return buf

    def _start(self):
        """루프 시작 — 페이드인이 구워진 머리를 먼저, 이어서 본체를 무한 반복."""
        g = max(0.0, min(1.0, (self._cur_speed - 30.0) / 500.0))   # 속도 0~1
        gain = (self.volume / 100.0) * (0.6 + 0.4 * g)
        self._loop_gain = gain
        fr2 = max(8000, int(self.fr * random.uniform(0.95, 1.08)))  # 획마다 피치만
        self._loop_fr = fr2
        wfx = _WAVEFORMATEX(1, 1, fr2, fr2 * 2, 2, 16, 0)
        wm = ctypes.windll.winmm
        h = ctypes.c_void_p()
        if wm.waveOutOpen(ctypes.byref(h), 0xFFFFFFFF, ctypes.byref(wfx), 0, 0, 0):
            return
        wm.waveOutSetVolume(h, 0xFFFFFFFF)     # 만땅 고정 — 페이드는 샘플에 있다
        head_buf = _scaled_buffer(self._head_pcm, gain, 2)
        hh = _WAVEHDR()                         # 1) 페이드인 머리 (한 번)
        hh.lpData = ctypes.cast(head_buf, ctypes.c_void_p)
        hh.dwBufferLength = len(self._head_pcm)
        wm.waveOutPrepareHeader(h, ctypes.byref(hh), ctypes.sizeof(_WAVEHDR))
        wm.waveOutWrite(h, ctypes.byref(hh), ctypes.sizeof(_WAVEHDR))
        body_buf = self._loop_buf(gain)
        hb = _WAVEHDR()                         # 2) 본체 (멈출 때까지 무한 반복)
        hb.lpData = ctypes.cast(body_buf, ctypes.c_void_p)
        hb.dwBufferLength = len(self.loop_pcm)
        hb.dwFlags = 0x00000004 | 0x00000008    # WHDR_BEGINLOOP | WHDR_ENDLOOP
        hb.dwLoops = 0xFFFFFFFF
        wm.waveOutPrepareHeader(h, ctypes.byref(hb), ctypes.sizeof(_WAVEHDR))
        wm.waveOutWrite(h, ctypes.byref(hb), ctypes.sizeof(_WAVEHDR))
        with self._lock:
            self._voice = (h, hh, hb, head_buf, body_buf)
            self._playing = True

    def _stop_loop(self, tail=True):
        """루프를 멈춘다. tail이면 페이드아웃 꼬리를 따로 재생해 부드럽게 끝낸다.

        **핸들을 먼저 꺼내 놓고(_voice=None) 그 다음에 닫는다.** 반대로 하면
        두 곳에서 동시에 들어왔을 때 같은 핸들을 두 번 닫아 access violation이
        난다. 꺼내기를 원자적으로 하면 두 번 닫는 일이 구조적으로 불가능하다.
        """
        with self._lock:
            voice, self._voice = self._voice, None
            self._playing = False
        if voice is None:
            return
        wm = ctypes.windll.winmm
        h, hh, hb, _hbuf, _bbuf = voice
        try:
            wm.waveOutReset(h)                  # 무한 반복 중단
            for hdr in (hh, hb):
                wm.waveOutUnprepareHeader(h, ctypes.byref(hdr),
                                          ctypes.sizeof(_WAVEHDR))
            wm.waveOutClose(h)
        except Exception:
            pass                                # 이미 닫혔어도 여기서 끝낸다
        if tail and self.volume > 0.0:          # 꼬리는 별도 장치 — 볼륨 간섭 없음
            buf = self._tail_buf(self._loop_gain)
            self._oneshot(buf, len(self._tail_pcm), self._loop_fr)

    def stop(self):
        self._stop_loop(tail=False)

    def close(self):
        """캐릭터 종료 시 — 재생 중인 것을 전부 정리한다."""
        self._stop_loop(tail=False)
        with self._lock:
            pending, self._oneshots = self._oneshots, []
        wm = ctypes.windll.winmm
        for h, hdr, _b in pending:
            try:
                wm.waveOutReset(h)
                wm.waveOutUnprepareHeader(h, ctypes.byref(hdr), ctypes.sizeof(_WAVEHDR))
                wm.waveOutClose(h)
            except Exception:
                pass


class _MacSoundPool:
    """macOS 소리 재생 — NSSound 사본을 돌려가며 겹쳐 재생한다.

    winmm(waveOut)은 윈도우 전용이라 맥에서는 AppKit의 NSSound를 쓴다.
    같은 NSSound를 연속 호출하면 이어붙지 않고 다시 시작되므로, 파일마다
    사본을 몇 개 두고 번갈아 재생해 타자처럼 빠른 연타도 겹치게 한다.
    """

    COPIES = 3

    def __init__(self, paths, volume):
        from AppKit import NSSound
        self.pool = []
        for p in paths:
            row = []
            for _ in range(self.COPIES):
                snd = NSSound.alloc().initWithContentsOfFile_byReference_(p, True)
                if snd is not None:
                    row.append(snd)
            if row:
                self.pool.append(row)
        if not self.pool:
            raise ValueError("재생 가능한 wav가 없음")
        self._turn = [0] * len(self.pool)
        self.set_volume(volume)

    def set_volume(self, volume):
        self.volume = max(0.0, min(float(volume), 100.0))
        g = self.volume / 100.0
        for row in self.pool:
            for snd in row:
                try:
                    snd.setVolume_(g)
                except Exception:
                    pass

    def _fire(self, idx):
        if self.volume <= 0 or not self.pool:
            return
        row = self.pool[idx % len(self.pool)]
        snd = row[self._turn[idx % len(self.pool)] % len(row)]
        self._turn[idx % len(self.pool)] += 1
        try:
            if snd.isPlaying():
                snd.stop()
            snd.play()
        except Exception:
            pass

    def _all_stop(self):
        for row in self.pool:
            for snd in row:
                try:
                    snd.stop()
                except Exception:
                    pass


class MacSoundPack(_MacSoundPool):
    """맥용 Mechvibes 팩 재생기 (SoundPack과 같은 인터페이스).

    맥은 어느 키를 눌렀는지 알 수 없어(카운터만 읽는다) 키별 구분은 못 한다.
    인자만 맞춰 두고 무시한다.
    """

    def play(self, key, code=None):
        return super().play(key)

    def __init__(self, folder, volume=60):
        with open(os.path.join(folder, "config.json"), encoding="utf-8") as fp:
            cfg = json.load(fp)
        if cfg.get("key_define_type", "multi") != "multi":
            raise ValueError("single 타입 팩 미지원")
        names, paths = [], []
        for v in cfg.get("defines", {}).values():
            if isinstance(v, str) and v and v not in names:
                names.append(v)
        for name in names:
            p = os.path.join(folder, name)
            if name.lower().endswith(".wav") and os.path.exists(p):
                paths.append(p)
        super().__init__(paths, volume)

    def play(self, key):
        self._fire(hash(str(key)) % max(len(self.pool), 1))

    def reap(self):
        pass                      # NSSound는 스스로 정리된다

    def close(self):
        self._all_stop()


class MacPenSound(_MacSoundPool):
    """맥용 펜 긋는 소리 (PenSound와 같은 인터페이스)."""

    def __init__(self, folder, volume=35):
        names = [f for f in sorted(os.listdir(folder)) if f.lower().endswith(".wav")]
        clips = [f for f in names if f.lower().startswith("clip")] or names
        paths = [os.path.join(folder, f) for f in clips]
        if not paths:
            raise ValueError("펜 소리 wav 없음")
        super().__init__(paths, volume)

    def play(self):
        self._fire(random.randrange(len(self.pool)))

    def stop(self):
        self._all_stop()


class PokeSound:
    """캐릭터를 눌렀을 때 나는 짧은 소리.

    누르는 건 잦아서 같은 소리가 그대로 반복되면 금방 물린다. 그래서 매번
    재생 속도를 조금씩 흔들어 음높이를 달리한다. 볼륨은 미리 곱해 두고
    (waveOutSetVolume은 드라이버가 무시할 수 있다) 재생 때는 고르기만 한다.
    """

    def __init__(self, folder, volume=40):
        import wave
        names = [f for f in sorted(os.listdir(folder)) if f.lower().endswith(".wav")]
        if not names:
            raise ValueError("클릭 소리 wav 없음")
        with wave.open(os.path.join(folder, names[0]), "rb") as w:
            if w.getsampwidth() != 2 or w.getnchannels() != 1:
                raise ValueError("클릭 소리는 16bit 모노 wav만 지원")
            self.fr = w.getframerate()
            self.pcm = w.readframes(w.getnframes())
        self._voices = []
        self.set_volume(volume)

    def set_volume(self, volume):
        self.volume = max(0.0, min(float(volume), 100.0))
        self.buf = (_scaled_buffer(self.pcm, self.volume / 100.0, 2)
                    if self.volume > 0 else None)

    def play(self):
        self.reap()
        if self.buf is None:
            return
        fr2 = max(8000, int(self.fr * random.uniform(0.92, 1.10)))
        wfx = _WAVEFORMATEX(1, 1, fr2, fr2 * 2, 2, 16, 0)
        wm = ctypes.windll.winmm
        h = ctypes.c_void_p()
        if wm.waveOutOpen(ctypes.byref(h), 0xFFFFFFFF, ctypes.byref(wfx), 0, 0, 0):
            return
        wm.waveOutSetVolume(h, 0xFFFFFFFF)     # 실볼륨은 샘플에 이미 반영됨
        hdr = _WAVEHDR()
        hdr.lpData = ctypes.cast(self.buf, ctypes.c_void_p)
        hdr.dwBufferLength = len(self.pcm)
        wm.waveOutPrepareHeader(h, ctypes.byref(hdr), ctypes.sizeof(_WAVEHDR))
        wm.waveOutWrite(h, ctypes.byref(hdr), ctypes.sizeof(_WAVEHDR))
        self._voices.append((h, hdr))

    def reap(self):
        wm = ctypes.windll.winmm
        keep = []
        for h, hdr in self._voices:
            if hdr.dwFlags & 0x00000001:        # WHDR_DONE
                wm.waveOutUnprepareHeader(h, ctypes.byref(hdr), ctypes.sizeof(_WAVEHDR))
                wm.waveOutClose(h)
            else:
                keep.append((h, hdr))
        self._voices = keep

    def close(self):
        wm = ctypes.windll.winmm
        for h, hdr in self._voices:
            try:
                wm.waveOutReset(h)
                wm.waveOutUnprepareHeader(h, ctypes.byref(hdr), ctypes.sizeof(_WAVEHDR))
                wm.waveOutClose(h)
            except Exception:
                pass
        self._voices = []


class MacPokeSound(_MacSoundPool):
    """맥용 클릭 소리 (PokeSound와 같은 인터페이스). 피치 변주는 없다."""

    def __init__(self, folder, volume=40):
        names = [f for f in sorted(os.listdir(folder)) if f.lower().endswith(".wav")]
        if not names:
            raise ValueError("클릭 소리 wav 없음")
        super().__init__([os.path.join(folder, names[0])], volume)

    def play(self):
        self._fire(0)

    def close(self):
        self._all_stop()


if IS_MAC:                        # 맥에서는 같은 이름으로 맥 구현을 쓴다
    SoundPack, PenSound, PokeSound = MacSoundPack, MacPenSound, MacPokeSound


if IS_WIN:
    ctypes.windll.user32.MonitorFromPoint.argtypes = [_POINT, ctypes.c_uint32]
    ctypes.windll.user32.MonitorFromPoint.restype = ctypes.c_void_p

_TK_ROOT = None                  # 맥에서 커서·화면 크기를 Tk로 얻기 위한 참조


class MacInput:
    """맥 입력 감지 — 리스너 스레드 대신 CoreGraphics 카운터를 매 프레임 읽는다.

    운영체제가 세어 둔 이벤트 개수를 그냥 조회하는 방식이라
      · 백그라운드 스레드가 없고 (크래시 원인 제거)
      · 손쉬운 사용 권한이 필요 없으며
      · 어느 스레드에서 불러도 안전하다.
    어떤 키가 눌렸는지는 알 수 없지만, 이 프로그램은 '몇 번 눌렸는가'만 쓴다.
    """

    HID = 1                      # kCGEventSourceStateHIDSystemState (실제 하드웨어)
    KEY_DOWN = 10
    MOVED, L_DRAG, R_DRAG = 5, 6, 7

    def __init__(self):
        cg = _MAC_CG
        if cg is None:
            raise RuntimeError("CoreGraphics 없음")
        cg.CGEventSourceCounterForEventType.restype = ctypes.c_uint32
        cg.CGEventSourceCounterForEventType.argtypes = [ctypes.c_uint32,
                                                        ctypes.c_uint32]
        cg.CGEventSourceButtonState.restype = ctypes.c_bool
        cg.CGEventSourceButtonState.argtypes = [ctypes.c_uint32, ctypes.c_uint32]
        self.cg = cg
        self.keys = self._count(self.KEY_DOWN)
        self.moves = self._moves()

    def _count(self, ev):
        return int(self.cg.CGEventSourceCounterForEventType(self.HID, ev))

    def _moves(self):
        return sum(self._count(e) for e in (self.MOVED, self.L_DRAG, self.R_DRAG))

    def read(self):
        """(눌린 키 수, 커서 움직임 수, 왼쪽 버튼 눌림) — 지난 호출 이후 변화량."""
        keys, moves = self._count(self.KEY_DOWN), self._moves()
        dk, self.keys = max(keys - self.keys, 0), keys
        dm, self.moves = max(moves - self.moves, 0), moves
        return dk, dm, bool(self.cg.CGEventSourceButtonState(self.HID, 0))


def cursor_pos():
    if IS_WIN:
        pt = _POINT()
        ctypes.windll.user32.GetCursorPos(ctypes.byref(pt))
        return pt.x, pt.y
    if _TK_ROOT is not None:      # 맥: Tk가 전역 커서 좌표를 알려준다
        try:
            return _TK_ROOT.winfo_pointerxy()
        except Exception:
            pass
    return 0, 0


def idle_seconds():
    """마지막 입력(마우스·키보드·펜) 이후 경과 초."""
    try:
        if IS_WIN:
            info = _LASTINPUTINFO()
            info.cbSize = ctypes.sizeof(_LASTINPUTINFO)
            ctypes.windll.user32.GetLastInputInfo(ctypes.byref(info))
            return max(ctypes.windll.kernel32.GetTickCount() - info.dwTime, 0) / 1000.0
        if _MAC_CG is not None:
            # kCGEventSourceStateCombinedSessionState=0, kCGAnyInputEventType=0xFFFFFFFF
            return float(_MAC_CG.CGEventSourceSecondsSinceLastEventType(
                0, 0xFFFFFFFF))
    except Exception:
        pass
    return 0.0


def foreground_process():
    """앞에 떠 있는 창의 프로세스 실행파일 이름 (소문자). 실패 시 ''."""
    try:
        if IS_WIN:
            u, k = ctypes.windll.user32, ctypes.windll.kernel32
            hwnd = u.GetForegroundWindow()
            pid = ctypes.c_ulong()
            u.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
            h = k.OpenProcess(0x1000, False, pid.value)  # QUERY_LIMITED_INFO
            if not h:
                return ""
            try:
                buf = ctypes.create_unicode_buffer(260)
                size = ctypes.c_ulong(260)
                if k.QueryFullProcessImageNameW(h, 0, buf, ctypes.byref(size)):
                    return os.path.basename(buf.value).lower()
            finally:
                k.CloseHandle(h)
        elif IS_MAC:
            return _mac_front_app()
    except Exception:
        pass
    return ""


def _mac_front_app():
    """맨 앞 앱 이름 (소문자). PyObjC가 있으면 그걸로, 없으면 빈 문자열."""
    try:
        from AppKit import NSWorkspace
        app = NSWorkspace.sharedWorkspace().frontmostApplication()
        if app is None:
            return ""
        name = app.localizedName() or app.bundleIdentifier() or ""
        return str(name).lower()
    except Exception:
        return ""


def mac_monitors():
    """맥에 붙어 있는 화면들의 사각형 목록.

    파이썬 추가 설치 없이 CoreGraphics를 직접 불러 쓴다. 실패하면 빈 목록을
    돌려주고, 부르는 쪽이 예전처럼 주 화면 하나로 넘어간다.
    """
    out = []
    if not IS_MAC:
        return out

    class _CGPoint(ctypes.Structure):
        _fields_ = [("x", ctypes.c_double), ("y", ctypes.c_double)]

    class _CGSize(ctypes.Structure):
        _fields_ = [("w", ctypes.c_double), ("h", ctypes.c_double)]

    class _CGRect(ctypes.Structure):
        _fields_ = [("origin", _CGPoint), ("size", _CGSize)]

    for path in ("/System/Library/Frameworks/CoreGraphics.framework/CoreGraphics",
                 "/System/Library/Frameworks/ApplicationServices.framework"
                 "/ApplicationServices"):
        try:
            cg = ctypes.cdll.LoadLibrary(path)
            n = ctypes.c_uint32(0)
            ids = (ctypes.c_uint32 * 16)()
            cg.CGGetActiveDisplayList.argtypes = [
                ctypes.c_uint32, ctypes.POINTER(ctypes.c_uint32 * 16),
                ctypes.POINTER(ctypes.c_uint32)]
            if cg.CGGetActiveDisplayList(16, ctypes.byref(ids),
                                         ctypes.byref(n)) != 0:
                continue
            cg.CGDisplayBounds.argtypes = [ctypes.c_uint32]
            cg.CGDisplayBounds.restype = _CGRect
            got = []
            for i in range(min(n.value, 16)):
                r = cg.CGDisplayBounds(ids[i])
                x, y = int(round(r.origin.x)), int(round(r.origin.y))
                w, h = int(round(r.size.w)), int(round(r.size.h))
                if w > 0 and h > 0:
                    got.append((x, y, x + w, y + h))
            if got:
                out = got
                break
        except Exception:
            continue
    return out


def list_monitors():
    """붙어 있는 화면들의 사각형 목록 — 왼쪽 위부터 차례로.

    듀얼 모니터에서 '어느 화면의 마우스를 따라갈지' 고르게 하려고 쓴다.
    """
    out = []
    if IS_WIN:
        try:
            proto = ctypes.WINFUNCTYPE(ctypes.c_int, ctypes.c_void_p,
                                       ctypes.c_void_p,
                                       ctypes.POINTER(_RECT), ctypes.c_double)

            def cb(hmon, hdc, lprc, data):
                mi = _MONITORINFO()
                mi.cbSize = ctypes.sizeof(_MONITORINFO)
                if ctypes.windll.user32.GetMonitorInfoW(hmon, ctypes.byref(mi)):
                    r = mi.rcMonitor
                    out.append((r.left, r.top, r.right, r.bottom))
                return 1
            ctypes.windll.user32.EnumDisplayMonitors(None, None, proto(cb), 0)
        except Exception:
            pass
    elif IS_MAC:
        out.extend(mac_monitors())
    if not out:
        out.append(monitor_at(0, 0))
    out.sort(key=lambda r: (r[1], r[0]))
    return out


def monitor_at(x, y):
    if IS_WIN:
        try:
            hmon = ctypes.windll.user32.MonitorFromPoint(_POINT(x, y), 2)
            mi = _MONITORINFO()
            mi.cbSize = ctypes.sizeof(_MONITORINFO)
            if ctypes.windll.user32.GetMonitorInfoW(hmon, ctypes.byref(mi)):
                r = mi.rcMonitor
                return r.left, r.top, r.right, r.bottom
        except Exception:
            pass
        u = ctypes.windll.user32
        return 0, 0, u.GetSystemMetrics(0), u.GetSystemMetrics(1)
    if IS_MAC:                    # 맥: 점이 들어 있는 화면을 찾는다
        for r in mac_monitors():
            if r[0] <= x < r[2] and r[1] <= y < r[3]:
                return r
    if _TK_ROOT is not None:      # 못 찾으면 주 화면 기준
        try:
            return (0, 0, _TK_ROOT.winfo_screenwidth(),
                    _TK_ROOT.winfo_screenheight())
        except Exception:
            pass
    return 0, 0, 1920, 1080


UPDATE_REPOS = {                 # 선물 캐릭터 자동 업데이트 배포 레포
    "parts_junsa": "rlfqjxm0-create/junsa-mascot",
    "parts_dog": "rlfqjxm0-create/dog-mascot",
    "parts_quincy": "rlfqjxm0-create/quincy-mascot",
    "parts_dororong_gift": "rlfqjxm0-create/dororong-mascot",
    "parts_saga": "rlfqjxm0-create/saga-mascot",
    "parts_gippo": "rlfqjxm0-create/gippo-mascot",
}


UPDATE_FLAG = ".updated"          # 업데이트 알림 신호 파일


def mark_updated(state_dir, restart, notes=None):
    """업데이트 사실을 남긴다. restart=True면 껐다 켜야 반영되는 경우.

    notes는 version.json에 실려 온 '이번에 바뀐 것' 목록(문자열 리스트).
    """
    try:
        items = [str(s).strip() for s in (notes or []) if str(s).strip()]
        with open(os.path.join(state_dir, UPDATE_FLAG), "w",
                  encoding="utf-8") as fp:
            json.dump({"restart": bool(restart), "notes": items[:6]}, fp,
                      ensure_ascii=False)
    except Exception:
        pass


def _take_update_flag(state_dir):
    """신호를 읽고 지운다 — 한 번만 알리기 위해. (말풍선 문구, 변경목록)."""
    p = os.path.join(state_dir, UPDATE_FLAG)
    if not os.path.exists(p):
        return None, []
    restart, notes = False, []
    try:
        with open(p, encoding="utf-8") as fp:
            d = json.load(fp)
        restart = bool(d.get("restart"))
        notes = [str(s) for s in (d.get("notes") or []) if str(s).strip()]
    except Exception:
        pass
    try:
        os.remove(p)
    except Exception:
        pass
    msg = ("업데이트 됐어요! 껐다 켜주세요" if restart
           else "새 버전으로 업데이트 됐어요!")
    return msg, notes


SEEN_FILE = ".seen_version"       # 마지막으로 알린 버전


def update_notice(char_dir, state_dir):
    """업데이트 직후인지 판단해 (말풍선 문구, 바뀐 점 목록)을 돌려준다.

    런처(exe에 구워진 코드)가 남기는 .updated 신호를 먼저 본다. 다만 런처는
    자동 업데이트 대상이 아니라서 옛 exe는 notes를 못 남긴다. 그래서
    version.json의 버전 변화를 여기서 직접 본다 — mascot.py는 자동 업데이트로
    갱신되므로, 친구에게 exe를 다시 보내지 않아도 이 경로는 동작한다.
    """
    msg, notes = _take_update_flag(state_dir)
    ver, vnotes, silent = None, [], False
    try:
        p = os.path.join(os.path.dirname(char_dir), "version.json")
        with open(p, encoding="utf-8") as fp:
            man = json.load(fp)
        ver = man.get("version")
        vnotes = [str(s) for s in (man.get("notes") or []) if str(s).strip()]
        # 조용한 배포 — 알릴 만한 변화가 아니라 팝업을 띄우지 않는다.
        # 런처(exe)는 자동 갱신이 안 돼서 늘 신호를 남기므로, 여기서 막는다.
        silent = bool(man.get("silent"))
    except Exception:
        pass
    if ver is None:
        return (None, []) if silent else (msg, notes)
    seen_path = os.path.join(state_dir, SEEN_FILE)
    seen = None
    try:
        with open(seen_path, encoding="utf-8") as fp:
            seen = json.load(fp).get("version")
    except Exception:
        pass
    if seen != ver:
        try:
            with open(seen_path, "w", encoding="utf-8") as fp:
                json.dump({"version": ver}, fp)
        except Exception:
            pass
        if seen is not None and not silent:   # 설치 후 첫 실행은 알릴 '변경'이 없다
            msg = msg or "새 버전으로 업데이트 됐어요!"
            notes = notes or vnotes
        if not silent:
            _update_log_add(state_dir, ver, vnotes or notes)
    return (None, []) if silent else (msg, notes)


UPDATE_LOG = ".update_log.json"   # 지난 업데이트 안내 보관 (최근 20개)


def _update_log_add(state_dir, ver, notes):
    """이번 안내를 기록에 남긴다. 못 보고 지나가도 나중에 되짚어 볼 수 있게."""
    notes = [str(x) for x in (notes or []) if str(x).strip()]
    if not notes:
        return
    path = os.path.join(state_dir, UPDATE_LOG)
    try:
        try:
            with open(path, encoding="utf-8") as fp:
                log = json.load(fp)
            log = log if isinstance(log, list) else []
        except Exception:
            log = []
        if log and log[-1].get("ver") == ver:
            log[-1]["notes"] = notes          # 같은 버전이면 갱신만
        else:
            log.append({"ver": ver, "notes": notes})
        with open(path, "w", encoding="utf-8") as fp:
            json.dump(log[-20:], fp, ensure_ascii=False)
    except Exception:
        pass


def _parts_broken(char_dir):
    """layout.json과 실제 PNG가 어긋나 있는지 = 업데이트가 중간에 끊긴 상태.

    기본 파츠뿐 아니라 패션 슬롯(skins/*) 폴더도 함께 확인한다.
    """
    dirs = [char_dir]
    skins = os.path.join(char_dir, "skins")
    if os.path.isdir(skins):
        dirs += [os.path.join(skins, d) for d in os.listdir(skins)
                 if os.path.isdir(os.path.join(skins, d))]
    for d in dirs:
        try:
            with open(os.path.join(d, "layout.json"), encoding="utf-8") as fp:
                layout = json.load(fp)
        except Exception:
            return True
        for name, info in layout.items():
            if not isinstance(info, dict) or "size" not in info:
                continue
            p = os.path.join(d, f"{name}.png")
            if not os.path.exists(p):
                return True
            try:
                with Image.open(p) as im:
                    if list(im.size) != list(info["size"]):
                        return True
            except Exception:
                return True
    return False


def repair_parts(char_dir, state_dir=None):
    """파츠가 섞여 있으면 배포 레포에서 다시 받아 맞춘다 (선물 exe 전용).

    자동 업데이트가 파일 하나씩 덮어쓰는 방식이라, 도중에 네트워크가 끊기면
    새 PNG + 옛 layout.json 처럼 섞인 상태로 남아 캐릭터가 깨져 보인다.
    실행할 때마다 정합성을 확인하고, 어긋나 있으면 여기서 복구한다.
    """
    repo = UPDATE_REPOS.get(os.path.basename(char_dir))
    if not (repo and getattr(sys, "frozen", False)):
        return                              # 개발 환경에서는 건드리지 않는다
    base_dir = os.path.dirname(char_dir)
    done = os.path.exists(os.path.join(base_dir, "version.json"))
    if done and not _parts_broken(char_dir):
        return                              # 정상 — 네트워크 접근 없음
    import hashlib
    import urllib.parse
    import urllib.request
    base = base_dir

    def fetch(rel):
        # 공백이 든 음원 폴더 경로 때문에 URL 인코딩이 필요하다
        url = (f"https://raw.githubusercontent.com/{repo}/main/"
               f"{urllib.parse.quote(rel, safe='/')}")
        req = urllib.request.Request(url, headers={"User-Agent": "mascot-repair"})
        for i in range(3):
            try:
                with urllib.request.urlopen(req, timeout=20) as r:
                    return r.read()
            except Exception:
                if i == 2:
                    raise
                time.sleep(1.0)

    changed = []
    try:
        man = json.loads(fetch("version.json").decode("utf-8"))
        for rel, want in man.get("files", {}).items():
            p = os.path.join(base, rel.replace("/", os.sep))
            try:
                with open(p, "rb") as fp:
                    if hashlib.sha256(fp.read()).hexdigest() == want:
                        continue
            except Exception:
                pass
            data = fetch(rel)
            if hashlib.sha256(data).hexdigest() != want:
                return                      # 내려받은 게 손상 — 다음 실행에 재시도
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "wb") as fp:
                fp.write(data)
            changed.append(rel)
        with open(os.path.join(base, "version.json"), "w", encoding="utf-8") as fp:
            json.dump(man, fp)
        if changed:
            # mascot.py는 이미 메모리에 올라와 있어 껐다 켜야 반영된다
            mark_updated(state_dir or char_dir, "mascot.py" in changed,
                         man.get("notes"))
    except Exception:
        pass                                # 오프라인이면 있는 그대로 실행


class TodoPanel:
    """캐릭터 왼쪽에 붙는 할 일 말풍선 창.

    본체 창은 캐릭터 크기에 맞춰져 있어 옆으로 그릴 자리가 없다. 그래서
    같은 색상키 투명을 쓰는 별도 창을 왼쪽에 두고 본체를 따라다니게 한다.
    말풍선을 우클릭하면 수정 / 완료 / 꼬리 방향 바꾸기를 고를 수 있다.
    """

    # 좁고 글자는 크게 — 화면을 덜 가리면서 잘 읽히게.
    # 맥은 같은 크기라도 글자가 더 넓게 그려져 조금 더 좁게 잡는다.
    W = 150 if IS_MAC else 160   # 패널 폭 (96DPI 기준)
    FS = 12                      # 글자 크기 (캐릭터 글자 크기 설정과는 무관)
    TAIL_W, TAIL_H = 17, 13      # 말풍선 꼬리 크기 (캐릭터 말풍선과 동일)
    PAD = TAIL_H + 8             # 간격 (꼬리가 다음 칸을 안 침범하게)

    # 우클릭 메뉴에서 고를 수 있는 배율 (%)
    ZOOMS = (60, 70, 80, 90, 100, 120, 140)

    def __init__(self, master, card, bg, on_done, on_move, on_edit=None,
                 offset=None, flip=False, on_flip=None, ui_k=1.0,
                 zoom=100, on_zoom=None, on_delete=None):
        # 화면 배율 반영 — 비율은 그대로 두고 통째로 키운다. 배율이 큰 화면에서
        # 폭·글자를 안 키우면 물리적으로 너무 작게 보인다. 다만 얼마나 커야
        # 편한지는 사람마다 달라서, 우클릭 메뉴에서 다시 조절할 수 있게 했다.
        self.ui_k = max(1.0, min(3.0, float(ui_k)))
        self.zoom = self._near_zoom(zoom)
        self.on_zoom = on_zoom
        self._scale()
        self.card = card
        self.on_done = on_done
        self.on_move = on_move
        self.on_edit = on_edit
        self.on_delete = on_delete   # 완료로 치지 않고 그냥 지우기
        self.on_flip = on_flip
        # 꼬리 방향 — 패널을 캐릭터 오른쪽에 두면 꼬리도 왼쪽을 봐야 한다
        self.flip = bool(flip)
        # 본체 창 왼쪽 위 모서리 기준 상대 위치 (끌어서 옮기면 갱신·저장).
        # 캐릭터 창과 겹치면 겹친 구간의 우클릭이 캐릭터한테 가서 설정 창이
        # 뜬다. 그래서 기본값은 딱 붙되 겹치지 않는 자리로 둔다.
        self._moved_by_user = bool(offset)
        self.offset = tuple(offset) if offset else (-(self.W + 4), 0)
        self.items = []          # [(말풍선 좌표, 할 일 인덱스)]
        self._hwnd_cache = None  # 창 핸들 (z순서 조정용)
        self.top = tk.Toplevel(master)
        self.top.overrideredirect(True)
        self.top.attributes("-topmost", True)
        if IS_MAC:
            try:
                self.top.attributes("-transparent", True)
            except Exception:
                pass
        else:
            self.top.attributes("-transparentcolor", bg)
        self.top.config(bg=bg)
        self.canvas = tk.Canvas(self.top, width=self.W, height=10, bg=bg,
                                highlightthickness=0)
        self.canvas.pack()
        self.canvas.bind("<Button-1>", self._press)
        self.canvas.bind("<B1-Motion>", self._drag)
        self.canvas.bind("<ButtonRelease-1>", self._release)
        self.canvas.bind("<Button-3>", self._menu)
        self.top.withdraw()
        self._pressed = None
        self._moved = False

    @classmethod
    def _near_zoom(cls, pct):
        """저장된 값이 이상해도 고를 수 있는 단계 중 가장 가까운 것으로."""
        try:
            pct = int(pct)
        except Exception:
            return 100
        return min(cls.ZOOMS, key=lambda z: abs(z - pct))

    def _scale(self):
        """화면 배율 × 사용자가 고른 배율로 치수를 다시 잡는다.

        인스턴스 값이 아니라 클래스에 적힌 기준값에서 매번 새로 계산한다.
        (인스턴스 값에서 다시 곱하면 배율을 바꿀 때마다 눈덩이처럼 커진다.)
        """
        k = self.k = self.ui_k * self.zoom / 100.0
        c = TodoPanel
        self.W = round(c.W * k)
        self.PAD = round(c.PAD * k)
        self.TAIL_W = round(c.TAIL_W * k)
        self.TAIL_H = round(c.TAIL_H * k)
        self.FS = max(7, round(c.FS * k))
        self.MENU_FS = max(7, round(9 * self.ui_k))   # 메뉴는 화면 배율만 따른다

    def set_zoom(self, pct):
        """할 일 목록만 키우거나 줄인다 (캐릭터·카드 크기와는 무관)."""
        pct = self._near_zoom(pct)
        if pct == self.zoom:
            return
        self.zoom = pct
        self._scale()
        try:
            self.canvas.config(width=self.W)
        except Exception:
            pass
        # 직접 옮긴 적이 없으면 폭이 바뀐 만큼 붙는 자리도 따라간다
        if not self._moved_by_user:
            self.offset = (-(self.W + 4), self.offset[1])
        if self.on_zoom is not None:
            self.on_zoom(self.zoom)

    def _rrect(self, x0, y0, x1, y1, r, **kw):
        """그냥 둥근 사각형 — 꼬리 때문에 모양이 일그러지지 않게 따로 그린다."""
        pts = []
        for cx, cy, a0, a1 in ((x1 - r, y0 + r, -90, 0), (x1 - r, y1 - r, 0, 90),
                               (x0 + r, y1 - r, 90, 180), (x0 + r, y0 + r, 180, 270)):
            for i in range(7):
                a = math.radians(a0 + (a1 - a0) * i / 6)
                pts.extend((cx + math.cos(a) * r, cy + math.sin(a) * r))
        return self.canvas.create_polygon(pts, smooth=True, **kw)

    def _tail(self, x0, x1, y1, r, fill, outline=None, dx=0, dy=0):
        """아래를 향한 날카로운 세모 꼬리. flip이면 왼쪽 아래를 본다.

        밑변을 말풍선 테두리 안쪽까지 덮어 그 구간의 테두리를 지우고,
        양 옆 빗변만 테두리 색으로 그어 이음새가 없게 만든다.
        """
        c = self.canvas
        tw, th = self.TAIL_W, self.TAIL_H
        s = -1 if self.flip else 1           # 꼬리가 향하는 쪽
        base = (x0 + r if self.flip else x1 - r) + dx   # 밑변의 바깥쪽 끝
        bin_ = base - tw * s                              # 밑변의 안쪽 끝
        by = y1 + dy
        tipx, tipy = base + th * 0.7 * s, by + th
        c.create_polygon(bin_, by - 2, tipx, tipy, base, by - 2,
                         fill=fill, outline="")
        if outline:
            c.create_line(bin_, by, tipx, tipy, fill=outline, width=2)
            c.create_line(tipx, tipy, base, by, fill=outline, width=2)


    def render(self, todos, tints=None):
        """항목을 위에서 아래로 쌓아 그린다. 창 높이도 함께 맞춘다.

        tints를 주면 그 항목의 테두리·글자 색을 바꾼다 (마감이 급할 때 등).
        """
        c, cd = self.canvas, self.card
        c.delete("all")
        self.items = []
        if not todos:
            self.top.withdraw()
            return
        tw = self.W - round(30 * self.k)   # 글자가 들어갈 폭
        heights = []                          # 먼저 줄바꿈 높이를 잰다
        for text in todos:
            t = c.create_text(0, 0, anchor="nw", text=text, width=tw,
                              font=("Malgun Gothic", self.FS))
            bb = c.bbox(t)
            heights.append(max(bb[3] - bb[1] + round(20 * self.k),
                               round(32 * self.k)))
            c.delete(t)

        y = self.PAD
        x0, x1 = round(8 * self.k), self.W - round(6 * self.k)
        for i, (text, h) in enumerate(zip(todos, heights)):
            r = round(13 * self.k)
            self._rrect(x0 + 2, y + 3, x1 + 2, y + h + 3, r,
                        fill="#e6e2e8", outline="")      # 그림자
            self._tail(x0 + 2, x1 + 2, y + h, r, "#e6e2e8", dx=0, dy=3)
            tint = (tints[i] if tints and i < len(tints) and tints[i]
                    else None)
            self._rrect(x0, y, x1, y + h, r, fill="#ffffff",
                        outline=tint or cd["border"], width=2)
            self._tail(x0, x1, y + h, r, "#ffffff", tint or cd["border"])
            mid = y + h / 2
            t = c.create_text((x0 + x1) / 2, mid, text=text, width=tw,
                              font=("Malgun Gothic", self.FS),
                              fill=tint or cd["text"], justify="center")
            tb = c.bbox(t)          # 실제 그려진 높이로 세로 중앙을 다시 맞춘다
            if tb:
                c.move(t, 0, round(mid - (tb[1] + tb[3]) / 2) - 1)
            self.items.append(((x0, y, x1, y + h), i))   # 우클릭 영역 = 말풍선
            y += h + self.PAD
        self.canvas.config(height=y)
        self.top.geometry(f"{self.W}x{int(y)}")
        self.top.deiconify()
        # 크기 변경이 실제로 반영된 뒤에 올린다 (바로 부르면 변경이 버려진다)
        self.top.after_idle(self.raise_above)

    def _press(self, e):
        self._pressed = (e.x, e.y, e.x_root, e.y_root)
        self._moved = False

    def _drag(self, e):
        """꾹 눌러 끌면 원하는 자리로 옮긴다."""
        if self._pressed is None:
            return
        px, py, prx, pry = self._pressed
        if not self._moved and abs(e.x_root - prx) + abs(e.y_root - pry) < 4:
            return
        self._moved = True
        self.top.geometry(f"+{e.x_root - px}+{e.y_root - py}")

    def _release(self, e):
        if self._pressed is None:
            return
        if self._moved:
            self.top.update_idletasks()      # 옮긴 좌표가 반영된 뒤 읽는다
            self.on_move(self.top.winfo_rootx(), self.top.winfo_rooty())
        # 왼쪽 버튼은 옮기기 전용 — 지우기는 우클릭 메뉴로만 (실수 방지)
        self._pressed = None

    def _at(self, x, y):
        """그 자리에 있는 할 일 번호 (없으면 None)."""
        for (x0, y0, x1, y1), idx in self.items:
            if x0 <= x <= x1 and y0 <= y <= y1:
                return idx
        return None

    def _menu(self, e):
        """말풍선 우클릭 — 수정 / 완료 / 삭제 / 꼬리 방향."""
        idx = self._at(e.x, e.y)
        if idx is None:
            return
        m = tk.Menu(self.top, tearoff=0,
                    font=("Malgun Gothic", self.MENU_FS))
        if self.on_edit is not None:
            m.add_command(label="수정", command=lambda: self.on_edit(idx))
        m.add_command(label="완료", command=lambda: self.on_done(idx))
        if self.on_delete is not None:
            # 완료와 다르다 — 축하도 기록도 없이 목록에서만 뺀다
            m.add_command(label="삭제", command=lambda: self.on_delete(idx))
        m.add_separator()
        m.add_command(label="꼬리 오른쪽으로" if self.flip else "꼬리 왼쪽으로",
                      command=self._toggle_flip)
        sub = tk.Menu(m, tearoff=0, font=("Malgun Gothic", self.MENU_FS))
        for z in self.ZOOMS:
            sub.add_command(label=("● " if z == self.zoom else "    ") + f"{z}%",
                            command=lambda p=z: self.set_zoom(p))
        m.add_cascade(label="크기 조절", menu=sub)
        self._menu_ref = (m, sub)       # 파이썬이 메뉴를 먼저 치우지 않게
        try:
            m.tk_popup(e.x_root, e.y_root)
        finally:
            m.grab_release()

    def _toggle_flip(self):
        """꼬리 방향만 뒤집는다 — 글자는 그대로다(뒤집으면 읽을 수 없으니)."""
        self.flip = not self.flip
        if self.on_flip is not None:
            self.on_flip(self.flip)

    def _hwnd(self):
        """이 창의 윈도우 핸들 (한 번 구해 두고 재사용)."""
        if self._hwnd_cache is None:
            try:
                self._hwnd_cache = (int(self.top.wm_frame(), 16)
                                    if IS_WIN else 0)
            except Exception:
                self._hwnd_cache = 0
        return self._hwnd_cache

    def raise_above(self):
        """캐릭터 창보다 위로 올린다.

        말풍선 창과 캐릭터 창이 둘 다 '항상 위'라, 캐릭터를 누르거나 창 순서가
        한 번 뒤집히면 캐릭터가 말풍선을 덮어 할 일이 안 보인다. 그래서 자리를
        잡을 때마다 다시 맨 앞으로 올려 둔다.
        """
        try:
            if IS_WIN:
                h = self._hwnd()
                if h:
                    # HWND_TOP(0), NOSIZE | NOMOVE | NOACTIVATE
                    ctypes.windll.user32.SetWindowPos(
                        h, 0, 0, 0, 0, 0, 0x1 | 0x2 | 0x10)
                    return
            self.top.lift()
        except Exception:
            pass

    def place(self, x, y):
        """본체 창 기준 저장된 자리에 붙인다 (끌어서 옮긴 위치)."""
        if self._moved and self._pressed is not None:
            return                      # 끄는 중에는 건드리지 않는다
        try:
            dx, dy = self.offset
            self.top.geometry(f"+{int(x + dx)}+{int(y + dy)}")
        except Exception:
            pass
        # 여기서 raise_above를 부르면 안 된다. Tk는 위치 변경을 미뤄 두었다가
        # 나중에 적용하는데, 그 전에 SetWindowPos로 창을 직접 건드리면 미뤄 둔
        # 이동이 버려져 말풍선이 캐릭터를 따라오지 못한다. z순서는 그리기
        # 루프가 주기적으로 맞춘다.

    def destroy(self):
        try:
            self.top.destroy()
        except Exception:
            pass


def _arc(center, point, deg):
    """point를 center를 축으로 deg만큼 돌린 자리 (팔 길이는 그대로)."""
    a = math.radians(deg)
    vx, vy = point[0] - center[0], point[1] - center[1]
    return (center[0] + vx * math.cos(a) - vy * math.sin(a),
            center[1] + vx * math.sin(a) + vy * math.cos(a))


class TrayIcon:
    """윈도우 알림 영역(트레이)에 캐릭터 머리 아이콘을 올린다.

    창이 테두리 없는 창이라 작업 표시줄에 안 잡히는데, 그러면 캐릭터를
    화면 밖으로 밀어 놓았을 때 되찾을 방법이 없다. 트레이에 두면 언제든
    부를 수 있다.

    메시지 창과 메시지 루프는 별도 스레드에서 돈다. Tk 쪽 일은 직접
    건드리지 않고 큐에 넣어, 그리기 루프가 꺼내 처리한다(다른 스레드에서
    Tk를 만지면 터진다).
    """
    _CLASS = "EnaMascotTrayWnd"
    _SEQ = 0                     # 한 프로세스에 여러 캐릭터가 떠도 안 겹치게
    WM_TRAY = 0x0400 + 42        # WM_APP+42

    def __init__(self, ico_path, tip, on_click, on_menu):
        self.ok = False
        if not IS_WIN:
            return
        self._ico, self._tip = ico_path, (tip or "")[:120]
        self._on_click, self._on_menu = on_click, on_menu
        self._hwnd = None
        self._added = False
        self._stop = False
        self._t = threading.Thread(target=self._run, daemon=True)
        self._t.start()
        for _ in range(50):          # 창이 만들어질 때까지 잠깐 기다린다
            if self._hwnd or self._stop:
                break
            time.sleep(0.02)
        self.ok = bool(self._hwnd)

    # ── 트레이 스레드 ────────────────────────────────────────────────
    def _run(self):
        import ctypes.wintypes as wt
        u = ctypes.windll.user32
        self._taskbar_msg = u.RegisterWindowMessageW("TaskbarCreated")

        # 64비트에서는 반환값·핸들이 c_long에 안 들어간다. 형을 안 정하면
        # DefWindowProc에 넘길 때 OverflowError가 나고 창이 먹통이 된다.
        LRESULT = ctypes.c_ssize_t
        WNDPROC = ctypes.WINFUNCTYPE(LRESULT, wt.HWND, wt.UINT,
                                     wt.WPARAM, wt.LPARAM)
        u.DefWindowProcW.argtypes = [wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM]
        u.DefWindowProcW.restype = LRESULT
        u.CreateWindowExW.restype = wt.HWND
        u.RegisterClassW.restype = ctypes.c_ushort

        def proc(hwnd, msg, wp, lp):
            if msg == self.WM_TRAY:
                low = lp & 0xFFFF
                if low in (0x0202, 0x0203):          # 왼쪽 클릭 / 더블클릭
                    self._safe_call(self._on_click)
                elif low in (0x0205, 0x007B):        # 오른쪽 클릭
                    self._safe_call(self._on_menu)
                return 0
            if msg == self._taskbar_msg:             # 탐색기가 다시 뜸
                self._added = False
                self._add()
                return 0
            if msg == 0x0002:                        # WM_DESTROY
                u.PostQuitMessage(0)
                return 0
            return u.DefWindowProcW(hwnd, msg, wp, lp)

        self._proc = WNDPROC(proc)                   # 참조를 붙잡아 둔다

        class WNDCLASS(ctypes.Structure):
            _fields_ = [("style", wt.UINT), ("lpfnWndProc", WNDPROC),
                        ("cbClsExtra", ctypes.c_int),
                        ("cbWndExtra", ctypes.c_int),
                        ("hInstance", wt.HINSTANCE), ("hIcon", wt.HICON),
                        ("hCursor", wt.HANDLE), ("hbrBackground", wt.HBRUSH),
                        ("lpszMenuName", wt.LPCWSTR), ("lpszClassName", wt.LPCWSTR)]

        try:
            hinst = ctypes.windll.kernel32.GetModuleHandleW(None)
            TrayIcon._SEQ += 1
            name = f"{self._CLASS}{os.getpid()}_{TrayIcon._SEQ}"
            wc = WNDCLASS()
            wc.lpfnWndProc = self._proc
            wc.hInstance = hinst
            wc.lpszClassName = name
            if not u.RegisterClassW(ctypes.byref(wc)):
                # 1410 = 이미 등록된 클래스. 그 경우는 그대로 써도 된다.
                if ctypes.windll.kernel32.GetLastError() != 1410:
                    self._stop = True
                    return
            self._hwnd = u.CreateWindowExW(0, name, name, 0, 0, 0, 0, 0,
                                           None, None, hinst, None)
            if not self._hwnd:
                self._stop = True
                return
            self._add()
            msg = wt.MSG()
            while u.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
                u.TranslateMessage(ctypes.byref(msg))
                u.DispatchMessageW(ctypes.byref(msg))
        except Exception:
            self._stop = True

    def _safe_call(self, fn):
        try:
            fn()
        except Exception:
            pass

    def _nid(self):
        import ctypes.wintypes as wt

        class NID(ctypes.Structure):
            _fields_ = [("cbSize", wt.DWORD), ("hWnd", wt.HWND),
                        ("uID", wt.UINT), ("uFlags", wt.UINT),
                        ("uCallbackMessage", wt.UINT), ("hIcon", wt.HICON),
                        ("szTip", wt.WCHAR * 128), ("dwState", wt.DWORD),
                        ("dwStateMask", wt.DWORD), ("szInfo", wt.WCHAR * 256),
                        ("uVersion", wt.UINT), ("szInfoTitle", wt.WCHAR * 64),
                        ("dwInfoFlags", wt.DWORD),
                        ("guidItem", ctypes.c_byte * 16),
                        ("hBalloonIcon", wt.HICON)]
        n = NID()
        n.cbSize = ctypes.sizeof(NID)
        n.hWnd = self._hwnd
        n.uID = 1
        return n

    def _add(self):
        u = ctypes.windll.user32
        try:
            hicon = u.LoadImageW(None, self._ico, 1, 0, 0, 0x00000010 | 0x00008000)
            n = self._nid()
            n.uFlags = 0x01 | 0x02 | 0x04            # MESSAGE | ICON | TIP
            n.uCallbackMessage = self.WM_TRAY
            n.hIcon = hicon
            n.szTip = self._tip
            if ctypes.windll.shell32.Shell_NotifyIconW(0, ctypes.byref(n)):
                self._added = True
        except Exception:
            pass

    def close(self):
        if not (IS_WIN and self._hwnd):
            return
        try:
            if self._added:
                ctypes.windll.shell32.Shell_NotifyIconW(2, ctypes.byref(self._nid()))
                self._added = False
            ctypes.windll.user32.PostMessageW(self._hwnd, 0x0010, 0, 0)  # WM_CLOSE
        except Exception:
            pass


def _end_anchors(im):
    """팔 그림의 위·아래 접합점 (가장 위/아래 불투명 줄의 가로 한가운데)."""
    a = im.split()[3]
    bb = a.getbbox()
    if not bb:
        return (im.width / 2, 0.0), (im.width / 2, float(im.height))

    def mid(y0, y1):
        r = a.crop((0, y0, im.width, y1)).getbbox()
        return (r[0] + r[2]) / 2 if r else im.width / 2

    top, bot = bb[1], bb[3] - 1
    return ((mid(top, min(top + 3, im.height)), float(top)),
            (mid(max(top, bot - 2), bot + 1), float(bot)))


ROLLOVER_HOURS = 6           # 작업일 경계 기본값 — 새벽 6시 이전은 전날로 친다


def _workday(ts=None, hour=ROLLOVER_HOURS):
    """그 시각이 속한 작업일 (YYYY-MM-DD).

    hour 이전이면 전날로 친다. 0으로 두면 달력 날짜 그대로.
    """
    t = time.localtime((ts if ts is not None else time.time()) - hour * 3600)
    return time.strftime("%Y-%m-%d", t)


def _screen_scale(root=None):
    """화면 배율 (150% 화면이면 1.5).

    Tk의 winfo_fpixels로 재면 두 가지에 걸린다 — scaling을 고정한 뒤에는 그
    값이 되돌아오고, 한 프로세스에서 창을 두 번째로 만들면 앞서 고정한 값이
    새어 96으로 나온다. 그래서 윈도우에 직접 물어본다.
    """
    if IS_WIN:
        u = ctypes.windll.user32
        try:                                  # 창이 놓인 모니터 기준 (가장 정확)
            if root is not None:
                hwnd = int(root.wm_frame(), 16)
                dpi = u.GetDpiForWindow(hwnd)
                if dpi:
                    return max(1.0, min(3.0, dpi / 96.0))
        except Exception:
            pass
        try:
            dpi = u.GetDpiForSystem()
            if dpi:
                return max(1.0, min(3.0, dpi / 96.0))
        except Exception:
            pass
    try:
        if root is not None:
            return max(1.0, min(3.0, root.winfo_fpixels("1i") / 96.0))
    except Exception:
        pass
    return 1.0


def already_running(char):
    """같은 캐릭터가 이미 떠 있으면 True. 실패하면 False(그냥 실행)."""
    if not IS_WIN:
        return False
    try:
        name = "ena-mascot-" + str(char)
        k = ctypes.windll.kernel32
        k.CreateMutexW.restype = ctypes.c_void_p
        h = k.CreateMutexW(None, False, name)
        if not h:
            return False
        if k.GetLastError() == 183:        # ERROR_ALREADY_EXISTS
            return True
        globals()["_INSTANCE_LOCK"] = h    # 프로세스가 살아 있는 동안 유지
    except Exception:
        return False
    return False


class Mascot:
    # 타이머 카드가 잘리지 않는 최소 창 폭 (카드 200 + 그림자·여백)
    CARD_MIN_W = 210

    def __init__(self, char_dir="parts", preview=False, state_dir=None):
        self.ox = 0.0                # 창이 카드 때문에 넓어진 만큼 캐릭터를 민다
        self.char_arg = char_dir
        self.dir = os.path.join(HERE, char_dir)
        self.char = os.path.basename(char_dir)
        # 설정·타이머 기록 저장 위치 (자동 업데이트로 교체되지 않는 곳으로 분리 가능)
        self.state_dir = state_dir or self.dir
        os.makedirs(self.state_dir, exist_ok=True)
        # 업데이트가 끊겨 파츠가 섞였으면 복구 (알림 신호도 여기서 남는다)
        repair_parts(self.dir, self.state_dir)
        with open(os.path.join(self.dir, "config.json"), encoding="utf-8") as fp:
            self.cfg = json.load(fp)

        # 사용자 환경설정 (config 기본값 위에 덮어씀)
        tcfg = self.cfg.get("timer") or {}
        self.us = dict(DEFAULT_SETTINGS)
        self.us["idle_sec"] = float(tcfg.get("idle_sec", self.us["idle_sec"]))
        self.settings_path = os.path.join(self.state_dir, ".settings.json")
        self._font_pct_saved = False
        try:
            with open(self.settings_path, encoding="utf-8") as fp:
                saved = json.load(fp)
            self._font_pct_saved = "font_pct" in saved
            self.us.update(saved)
        except Exception:
            pass
        self._sanitize_settings()

        # 패션(스킨) 슬롯 — 파츠만 다른 폴더에서 읽고 설정·기록은 그대로 공유
        self.skins = self.cfg.get("skins") or [{"name": "기본", "dir": ""}]
        self.skin_names = [s.get("name") or f"슬롯 {i + 1}"
                           for i, s in enumerate(self.skins)]
        want = self.us.get("skin")
        idx = self.skin_names.index(want) if want in self.skin_names else 0
        sub = (self.skins[idx].get("dir") or "").strip()
        self.skin_name = self.skin_names[idx]
        self.parts_dir = os.path.join(self.dir, *sub.split("/")) if sub else self.dir
        if not os.path.exists(os.path.join(self.parts_dir, "layout.json")):
            self.parts_dir, self.skin_name = self.dir, self.skin_names[0]
        self.us["skin"] = self.skin_name
        with open(os.path.join(self.parts_dir, "layout.json"), encoding="utf-8") as fp:
            self.layout = json.load(fp)
        # 파츠 자리 미세 보정 (캔버스 px). layout.json은 PSD에서 다시 뽑을 때마다
        # 덮어써지므로, 손으로 맞춘 값은 config에 둬야 남는다.
        for name, off in (self.cfg.get("part_offsets") or {}).items():
            spot = self.layout.get(name)
            if isinstance(spot, dict) and spot.get("pos"):
                spot["pos"] = [spot["pos"][0] + off[0], spot["pos"][1] + off[1]]
        # 펜이 닿는 영역은 책상 그림에 붙은 값이라, 옷마다 책상 자리가
        # 조금 다르면 옷별로 따로 둬야 한다 (안 그러면 그 옷에서만 펜이 밀린다).
        # skins 항목의 screen_quad가 있으면 그것을 쓰고, 없으면 공용 값.
        self._quad_src = (self.skins[idx].get("screen_quad")
                          if self.skin_name == self.skin_names[idx] else None) \
            or self.cfg["screen_quad"]

        s = self.s = float(self.cfg.get("scale", 1.0)) * self.us["scale_pct"] / 100.0
        self.timer_on = bool(tcfg.get("enabled")) \
            if self.us["show_timer"] is None else bool(self.us["show_timer"])
        self.idle_thr = float(self.us["idle_sec"])
        self._settings_win = None

        # 타이머 카드 테마 (캐릭터별 config의 card 섹션)
        cc = self.cfg.get("card") or {}
        self.card = {
            "bg": cc.get("bg", "#ffffff"), "border": cc.get("border", CARD_BORDER),
            "text": cc.get("text", CARD_NAVY), "sub": cc.get("sub", CARD_GRAY),
            "track": cc.get("track", CARD_TRACK), "fill": cc.get("fill", CARD_FILL),
            "deco": cc.get("deco", "panda"),
            # 설정·브리핑 창 배경 (캐릭터 테마에 맞춰 바꿀 수 있게)
            "panel": cc.get("panel", "#fffdfe"),
            "soft": cc.get("soft", "#fbf3f7"),
            "line": cc.get("line", "#f0e6ec"),
        }

        # 워크스페이스 워크타이머 연동 (config의 workspace_timer = 라이브 파일 경로)
        # 연동 모드 = 게이지 대신 시계 토글 카드. 비연동(준사) = 목표 게이지 카드.
        ws = self.cfg.get("workspace_timer")
        self.ws_path = os.path.normpath(os.path.join(HERE, ws)) if ws else None
        self._ws_data = None
        self._ws_read = 0.0
        self._ws_lost = False        # 기존 타이머가 꺼져 자체 측정으로 넘어갔는지
        self._solo_from = 0.0        # 혼자 재기 시작한 시점의 누적 시간
        # ── 스트레칭 알림 (누를 때까지 안 꺼진다) ────────────────────────
        self.stretch_pending = False # 알림이 아직 살아 있는가
        self.stretch_shown = 0.0     # 화면에 실제로 보인 시간 (안 보이면 안 흐름)
        self.stretch_replay = 0.0    # 다음으로 기지개를 다시 켤 시각
        self._stretch_line = ""      # 알림 말풍선 문구
        self._stretch_last = 0.0     # 지난 프레임 시각 (보인 시간 계산용)
        self._stretch_hover = False  # 커서가 캐릭터 위에 있는가
        self._settings_open = None   # 환경설정에서 펼쳐 놓은 목록의 키
        self._fb_msg = ""            # 건의 보내기 결과 문구
        self._fb_last = 0.0          # 마지막으로 보낸 시각 (연타 방지)
        self.zero_at = 0.0           # 작업 종료를 누른 시점의 누적 — 여기서부터 다시 센다
        self.goal_cheered = ""       # 목표 달성을 축하한 작업일
        # ── 마감 목록 (할 일 목록과 같은 말풍선 구조, 여러 개 등록) ──────
        self.dues = []               # [{"name": ..., "date": "YYYY-MM-DD"}]
        self.due_pos = None
        self.due_flip = False
        self.due_zoom = 100
        self.due_panel = None
        self._due_shown = ""         # 마지막으로 그린 날짜 (자정 넘으면 다시 그림)
        self._beat_t = 0.0           # 살아있음 알림을 마지막으로 쓴 시각
        self._pid_written = False    # PID 파일을 남겼는가
        self.has_clock = self.timer_on and self.ws_path is not None
        self.clock_open = bool(self.us.get("clock_open")) if self.has_clock else False

        self.font_k = 1.0        # 창을 만든 뒤 화면 배율을 보고 다시 정한다
        self.oy = self._timer_oy()                  # 캐릭터 전체 y 오프셋
        cw, ch = self.layout["canvas"]
        self.cw_px, self.ch_px = round(cw * s), round(ch * s)
        # 타이머 카드는 글자 크기 때문에 폭이 고정(200px)이라, 캐릭터를 작게
        # 줄이면 창이 카드보다 좁아져 카드 양옆이 잘린다. 창을 카드가 들어갈
        # 만큼은 넓혀 두고, 남는 폭만큼 캐릭터를 가운데로 민다(ox).
        self.W = max(self.cw_px, self.CARD_MIN_W if self.timer_on else 0)
        self.ox = (self.W - self.cw_px) / 2
        self.H = self.ch_px + self.oy

        self.root = tk.Tk()
        globals()["_TK_ROOT"] = self.root      # 커서·화면 크기 조회용
        # 글자 크기를 화면 배율과 무관하게 고정한다. Tk는 포인트로 지정한
        # 글꼴을 화면 DPI에 맞춰 키우는데, 이 프로그램의 카드·말풍선·패널은
        # 전부 픽셀 단위로 짜여 있어서 배율이 높은 화면에서는 글자만 커져
        # 서로 겹친다(175%부터 '딴짓 중'과 시간이 포개짐). 96DPI 기준으로
        # 못 박아 어느 화면에서도 설계한 그대로 나오게 한다.
        self.ui_k = _screen_scale(self.root)
        try:
            self.root.tk.call("tk", "scaling", 96.0 / 72.0)
        except Exception:
            pass
        # 처음 켜는 사람은 화면 배율에 맞춘 크기로 시작한다 (설정한 적이 있으면 존중)
        if not self._font_pct_saved:
            self.us["font_pct"] = max(70, min(160, round(self.ui_k * 100)))
        self.font_k = max(0.7, min(1.6,
                                   float(self.us.get("font_pct", 100)) / 100.0))
        self.root.overrideredirect(True)
        self.root.attributes("-topmost", bool(self.us["topmost"]))
        # 투명 배경: 윈도우는 색상키, 맥은 Tk의 진짜 투명 속성
        bg = TRANSPARENT
        if IS_MAC:
            bg = self._setup_mac_window()
        else:
            self.root.attributes("-transparentcolor", TRANSPARENT)
        self.canvas_bg = bg
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        self.ui_prefs_path = os.path.join(self.state_dir, ".ui_prefs.json")
        self.win_pos = self._load_win_pos(sw, sh)
        wx, wy = self.win_pos
        self.root.geometry(f"{self.W}x{self.H}+{wx}+{wy}")

        kw = {"bg": bg} if bg else {}
        self.canvas = tk.Canvas(self.root, width=self.W, height=self.H,
                                highlightthickness=0, **kw)
        self.canvas.pack()
        if IS_MAC:                            # 제목 표시줄 제거 후 위치 재적용
            self._mac_borderless()
            self.root.geometry(f"{self.W}x{self.H}+{wx}+{wy}")

        self._tw_cache = {}          # 상태 텍스트 폭 캐시 (캔버스로 측정)

        # ── 할 일 메모 (config의 "todo") ─────────────────────────────────
        self.todo_on = bool(self.cfg.get("todo"))
        self.todos = []
        self.todo_pos = None         # 본체 기준 패널 위치 (끌어서 옮긴 자리)
        self.todo_flip = False       # 말풍선 꼬리가 왼쪽을 보는가
        self.todo_zoom = 100         # 할 일 목록만의 배율 (우클릭 → 크기 조절)
        self.todo_panel = None
        self.todo_path = os.path.join(self.state_dir, ".todos.json")
        if self.todo_on:
            self._todo_load()
            self.todo_panel = TodoPanel(self.root, self.card, bg,
                                        self._todo_done, self._todo_moved,
                                        self._todo_edit, self.todo_pos,
                                        self.todo_flip, self._todo_flipped,
                                        self.ui_k, self.todo_zoom,
                                        self._todo_zoomed,
                                        on_delete=self._todo_delete)
            self.root.after(250, self._todo_refresh)   # 창 위치가 잡힌 뒤 배치

        # ── 마감 목록 (config의 "deadline_on") ───────────────────────────
        if self.cfg.get("deadline_on"):
            self._due_load()
            self.due_panel = TodoPanel(
                self.root, self.card, bg, self._due_remove, self._due_moved,
                self._due_edit,
                self.due_pos or (self.W + 4, 0),   # 기본은 캐릭터 오른쪽
                self.due_flip, self._due_flipped, self.ui_k, self.due_zoom,
                self._due_zoomed)
            self.due_panel._moved_by_user = bool(self.due_pos)
            self.root.after(280, self._due_refresh)

        # ── 귀여운 이벤트 (선물 캐릭터 전용 — config의 "fun") ────────────
        self.fun = bool(self.cfg.get("fun"))
        # 말풍선·클릭 반응만 따로 켤 수 있게 (fun을 켜면 자동 포함)
        self.can_talk = bool(self.fun or self.cfg.get("poke")
                             or self.cfg.get("records"))
        self.can_cheer = bool(self.fun or self.cfg.get("records"))
        self.bubble = None           # (텍스트, 사라질 시각)
        self.particles = []          # 폭죽 조각 [x, y, vx, vy, 색, 수명]
        self.hat_until = 0.0         # 고깔모자 표시 종료 시각
        self.smile_until = 0.0       # 웃는 표정 종료 시각
        self.celebrate_until = 0.0   # 축하 연출 종료 시각
        # ── 제스처 (config의 "gestures") ──────────────────────────────────
        # 값은 전부 여기서 초기화한다. 조건문 뒤에서 처음 만들면 draw() 중에
        # 없는 이름을 찾다 예외가 나고, 캐릭터가 사라지고 그림자만 남는다.
        self.gestures_on = bool(self.cfg.get("gestures"))
        self.gest = None             # 진행 중인 동작 이름
        self.gest_t0 = 0.0           # 시작 시각
        self.gest_dur = 0.0          # 동작 길이(초)
        self._g_dy = 0.0             # 이번 프레임 몸 전체 상하 이동
        self._g_hdy = 0.0            # 이번 프레임 머리만 상하 이동 (끄덕임)
        self._g_tilt = 0.0           # 이번 프레임 머리 기울기(도)
        self._g_hands = None         # 이번 프레임 손 이동량 (없으면 평소대로)
        self._g_eyes_shut = False    # 이번 프레임 눈을 감고 있는가 (기지개)
        self._g_smile = False        # 이번 프레임 웃는 얼굴인가 (리듬 타기)
        self.gest_groove_next = 0.0  # 다음 리듬 타기 시각
        self.gest_stretch_next = 0.0 # 다음 기지개 시각
        self.gest_wave_next = 0.0    # 작업 시작 인사 쿨다운
        self._last_state = "idle"    # 지난 프레임의 타이머 상태
        self.notes = []              # 음표 [x, y, vx, vy, 종류, 남은프레임, 총]
        self._note_next = 0.0        # 다음 음표가 튀어나올 시각
        self._note_left = 0          # 이번 리듬 타기에 남은 음표 수
        self.fx_imgs = {}            # 종류별 파티클 그림 (음표·하트·땀…)
        self._doze_woke = False      # 이번 꾸벅에서 이미 깼는가
        self._yawn_next = 0.0        # 다음 하품을 볼 수 있는 시각
        self._doze_next = 0.0        # 다음 꾸벅
        self._think_next = 0.0       # 다음 생각
        self._sway_next = 0.0        # 다음 좌우 흔들기
        self._heart_next = 0.0       # 다음 하트 (작업 중에만)
        self._fail = {}              # 구역별 실패 횟수 (3회면 그 구역만 끔)
        self._fail_at = {}           # 구역별 마지막 실패 시각 (한참 지나면 재시도)
        self._sleeping = False       # 자는 중이면 프레임을 줄인다
        # 기록 갱신 축하 — '오늘'의 기준은 시각이 아니라 한 세션
        # (작업 시작 ~ '작업 종료' 버튼). 종료하면 새 세션으로 다시 센다.
        self.rec = {"strokes": [], "focus": 0.0}
        self._rec_prev_run = 0.0
        self._rec_armed = True       # 이번 집중 구간에서 아직 축하 안 함
        self._rec_next = 0.0         # 축하 쿨다운 (연달아 뜨지 않게)
        self._update_msg, self._update_notes = update_notice(self.dir,
                                                             self.state_dir)
        self._update_win = None      # 업데이트 안내 팝업 (한 번만)
        # 펜 추적 진단 (config의 pen_diag를 켠 캐릭터만). 어느 화면으로
        # 판단하는지 파일에 남긴다 — 맥 다중 모니터 문제를 보려는 것.
        self._diag_left = self.PEN_DIAG_MAX if self.cfg.get("pen_diag") else 0
        self._diag_last = None       # 마지막으로 기록한 화면 사각형
        # 머리 자리 진단 (config의 head_diag를 켠 캐릭터만)
        self._hd_left = self.HEAD_DIAG_MAX if self.cfg.get("head_diag") else 0
        self._hd_head = False        # 첫머리를 남겼는가
        self._hd_at = 0.0
        self._diag_at = 0.0          # 마지막으로 기록한 시각
        self.shadow_img_type = None  # 타자 자세용 그림자 (깃펜 없음)
        self._shadow_base = None
        self._shadow_typing = False
        self._shadow_want = False    # 바꾸고 싶은 상태 (아직 확정 전)
        self._shadow_since = 0.0     # 그 상태가 유지된 시각
        self._shadow_swap = 0.0      # 마지막으로 실제 교체한 시각
        self._pen_draw = None        # 펜 손을 머리 뒤에 그릴 때 쓰는 임시 보관
        self._pet_drawn = []         # 이번 프레임에 그린 반려동물 (그림자용)
        self._tick_after = None      # 예약해 둔 다음 프레임 (종료할 때 취소)
        self._pet_sh_cache = {}
        self._pet_sh_on = False
        self._pet_sh_t = 0.0
        self.click_bounce = 0.0      # 클릭 반응 튀어오름 종료 시각
        self.pet_t0 = 0.0            # 반려동물 등장 시작(0=쉬는 중)
        _now = time.time()
        self.next_talk = _now + random.uniform(120, 300)
        self._recent_talk = []       # 최근에 한 말 (연달아 반복 방지)
        self.next_pet = _now + random.uniform(30, 80)   # 첫 인사는 좀 이르게
        # 하루 브리핑용 집계
        self.stat = {"work": 0.0, "other": 0.0, "idle": 0.0, "keys": 0,
                     "strokes": 0, "best": 0.0, "_run": 0.0,
                     "first": 0.0, "last": 0.0}

        self.prop_name = None        # 이번 실행에 뽑힌 소품 (_load_parts가 채움)
        self.prop_dir = self.parts_dir   # 소품 PNG를 읽을 폴더
        self._prop_layout = self.layout  # 소품 좌표가 든 layout
        self._back_cache = {}        # 몸 뒤 파츠 움직임 프레임 (칸별로만 만든다)
        # 파츠별 움직임 상태 — 기뽀처럼 기본 날개와 소품 날개가 같이 있을 때
        # 서로 다른 박자로 움직이도록 이름별로 따로 든다
        self._back_st = {}
        self._prop_back_cfg = {}     # 뽑힌 소품의 뒤쪽 조각 움직임 설정
        self._load_parts()

        # ── 상태 ──────────────────────────────────────────────────────────
        self.key_events = 0
        self._seen_keys = 0
        self.squash_until = 0.0
        self.mouse_pressed = False
        self.last_drag = 0.0
        self.last_pointer = 0.0
        self.last_key = 0.0
        self.tap_side = False
        self.key_ang_t = 0.0
        self.key_ang = 0.0
        self.left_down_until = 0.0
        self.pen_ang_t = 0.0
        self.pen_ang = 0.0
        self.pen_down_until = 0.0
        self.strokes = []
        self._new_stroke = True
        self.blink_until = 0.0
        self.next_blink = time.time() + random.uniform(2.5, 5.5)
        self._pen_xy = list(self.pen_base_tip)
        self._force = {}

        # ── 타이머 상태 ───────────────────────────────────────────────────
        self.work_secs = 0.0
        self._t_last = time.time()
        self._t_save = 0.0
        self._fg_checked = 0.0
        self._fg_work = False
        self.state_path = os.path.join(self.state_dir, ".timer_state.json")
        if self.timer_on and self.ws_path is None:
            self._timer_load()

        # ── 창 드래그 이동 / 카드 클릭 토글 / 우클릭 메뉴 ────────────────
        self._press = None
        self._dragged = False
        self.canvas.bind("<Button-1>", self._on_press)
        self.canvas.bind("<B1-Motion>", self._on_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_release)
        menu = tk.Menu(self.root, tearoff=0, font=self._uf(9))
        if self.todo_on:
            menu.add_command(label="할 일 추가", command=self.add_todo)
        if self.cfg.get("deadline_on"):
            menu.add_command(label="마감 추가", command=self.add_due)
        if self.todo_on or self.cfg.get("deadline_on"):
            menu.add_separator()
        if self.ws_path is not None:
            menu.add_command(label="작업 종료", command=self._end_workday)
        menu.add_command(label="환경설정", command=self.open_settings)
        if self.has_clock:
            menu.add_command(label="시계 펼치기 / 접기", command=self._toggle_clock)
        if self.timer_on and self.ws_path is None:
            menu.add_command(label="타이머 초기화", command=self._timer_reset)
        menu.add_separator()
        menu.add_command(label="종료", command=self.close)
        self._menu = menu            # 트레이 아이콘에서도 같은 메뉴를 쓴다
        # grab_release를 안 하면 메뉴를 닫은 뒤에도 마우스를 붙잡고 있어
        # 다음 클릭이 엉뚱하게 먹힌다
        def _pop(e):
            try:
                menu.tk_popup(e.x_root, e.y_root)
            finally:
                menu.grab_release()

        self.canvas.bind("<Button-3>", _pop)
        self.tray = None
        self._tray_q = []            # 트레이 스레드가 넣고 그리기 루프가 뺀다
        self._safe("tray", self._tray_setup)

        # ── 타자 소리 / 펜 소리 ──────────────────────────────────────────
        self.sndpack = None
        self.pensnd = None
        self.pokesnd = None
        self._pen_playing = False
        self._pen_release_t = None
        # 그레인 펜 소리 — 획 감지·재생은 마우스 콜백(_on_click/_on_move)에서,
        # 페이드 진행과 루프 전환은 그리기 루프의 tick()에서 한다.
        self._pen_grain = False
        self.sound_packs = self._list_packs()
        self._init_sound()

        # ── 전역 입력 리스너 ──────────────────────────────────────────────
        self._held = set()
        self._key_times = {}          # 키별 마지막 눌림 시각 (다이얼 연타 감지)
        self._kb = self._ms = self._macin = None
        if keyboard is not None:                  # 윈도우: 전역 후킹 리스너
            self._kb = keyboard.Listener(on_press=self._on_key,
                                         on_release=self._on_key_release)
            self._ms = mouse.Listener(on_click=self._on_click,
                                      on_move=self._on_move)
            self._kb.daemon = self._ms.daemon = True
            self._kb.start()
            self._ms.start()
        else:                                     # 맥: 매 프레임 카운터 폴링
            try:
                self._macin = MacInput()
            except Exception:
                self._macin = None

        # ── 그림자 레이어 창 ─────────────────────────────────────────────
        self.root.update_idletasks()
        self._main_hwnd = int(self.root.wm_frame(), 16) if IS_WIN else 0
        self.shadow = None
        self._z_check = 0.0
        self._panel_z = 0.0          # 말풍선 창을 다시 올린 시각
        if self.shadow_img is not None and IS_WIN:
            # 그림자 이미지가 P만큼 여백을 두므로, 창을 (offset - P)에 놓아 정렬
            self.shadow = ShadowLayer(self.root, self.shadow_img,
                                      offset=(7 - SHADOW_PAD, 9 - SHADOW_PAD))
            self.shadow.place(self.root.winfo_rootx(), self.root.winfo_rooty(),
                              self._main_hwnd)
        self._last_pos = None

        self._apply_autostart()          # exe 배포본이면 시작프로그램 등록
        self._pen_diag_head()            # config의 pen_diag가 켜졌을 때만

        if os.environ.get("MASCOT_DEBUG") == "1":
            self.root.after(4000, self._dump_debug)

        if preview:
            self.root.after(600, self._preview_shots)
        else:
            self.tick()

    # ── 파츠 로드 (모든 좌표는 표시 배율 + y 오프셋 적용) ─────────────────
    # 밑그림 위에만 놓이는지 검사할 파츠들 (얼굴 위에 얹히는 것들)
    COVER_CHECK = ("pupils", "lashes", "eyes_closed", "hair", "smile")

    def _find_covered_parts(self):
        """'밑그림에 완전히 덮이는' 파츠 이름들.

        캐릭터마다 그림이 달라서 사람이 정하지 않고 실제 픽셀로 확인한다.
        한 픽셀이라도 밑그림 밖으로 나가면 그 파츠는 배경과 닿으므로 제외한다.
        """
        if not self.cfg.get("soft_overlay"):
            return set()
        from PIL import ImageChops
        try:
            base = "head" if (self.has_part("head")) else "body_open"
            cw, ch = self.layout["canvas"]

            def mask(name, thr):
                path = os.path.join(self.parts_dir, f"{name}.png")
                a = Image.open(path).convert("RGBA").getchannel("A")
                sheet = Image.new("L", (cw, ch), 0)
                sheet.paste(a.point(lambda v: 255 if v >= thr else 0),
                            tuple(self.layout[name]["pos"]))
                return sheet

            solid = mask(base, 250)
            out = set()
            for n in self.COVER_CHECK:
                if not self.has_part(n) or n == base:
                    continue
                outside = ImageChops.subtract(mask(n, 1), solid)
                if outside.getbbox() is None:
                    out.add(n)
            return out
        except Exception:
            self._log_error("cover_check")
            return set()

    def _covered_by_base(self, lay, path):
        """그 그림이 밑그림(머리/몸통) 안에만 들어가는가 — 소품처럼 파일 경로로."""
        if not self.cfg.get("soft_overlay"):
            return False
        from PIL import ImageChops
        try:
            base = "head" if self.has_part("head") else "body_open"
            cw, ch = self.layout["canvas"]
            solid = Image.new("L", (cw, ch), 0)
            ba = Image.open(os.path.join(self.parts_dir,
                                         f"{base}.png")).convert("RGBA")
            solid.paste(ba.getchannel("A").point(lambda v: 255 if v >= 250 else 0),
                        tuple(self.layout[base]["pos"]))
            mine = Image.new("L", (cw, ch), 0)
            ia = Image.open(path).convert("RGBA")
            mine.paste(ia.getchannel("A").point(lambda v: 255 if v else 0),
                       tuple(lay["pos"]))
            return ImageChops.subtract(mine, solid).getbbox() is None
        except Exception:
            return False

    def has_part(self, name):
        """그 파츠의 PNG와 layout이 둘 다 있는가 (파츠 불러오기 전에도 쓴다)."""
        return (name in self.layout
                and os.path.exists(os.path.join(self.parts_dir, f"{name}.png")))

    def _hard(self, im):
        """반투명 가장자리 픽셀 이분화 — 색상키 투명의 어두운 테두리(fringe) 방지.

        밝은 캐릭터가 어두운 배경에서 회색 테두리가 지는 문제를, 가장자리 알파를
        50% 기준으로 켜고 끄는 이분화로 없앤다(부드럽진 않지만 테두리가 안 생김).
        """
        if not self.cfg.get("hard_alpha"):
            return im
        from PIL import ImageChops, ImageFilter
        im = self._avoid_key(im)
        a = im.getchannel("A")
        solid = a.point(lambda v: 255 if v >= 128 else 0)
        # 반투명하게 그려진 '내부 선'(옅은 음영 등)은 살린다 — 주변이 대부분
        # 불투명하면 실루엣 안쪽이라는 뜻. 알파 0인 진짜 빈틈은 건드리지 않는다.
        im = im.copy()
        if not self.cfg.get("soft_inner"):
            # 기본: 알파만 이분화한다. 반투명·투명한 안쪽을 억지로 불투명하게
            # 만들면 그 자리의 어두운 색이 드러나 검은 얼룩이 된다
            # (도로롱 머리카락 사건). 구멍 메우기도 같은 이유로 하지 않는다.
            im.putalpha(solid)
            return im
        near = solid.filter(ImageFilter.GaussianBlur(2))
        inner = ImageChops.multiply(
            a.point(lambda v: 255 if 0 < v < 128 else 0),
            near.point(lambda v: 255 if v >= 150 else 0))
        if inner.getbbox():
            # 그냥 불투명하게 만들면 옅게 그린 어두운 색이 진하게 드러나
            # 검은 얼룩이 된다(도로롱 머리카락 사건). 주변 색 위에 그 알파로
            # 얹은 결과로 바꿔, 원래 눈에 보이던 색을 유지한다.
            rgb = im.convert("RGB")
            base = rgb.filter(ImageFilter.GaussianBlur(4))
            blended = Image.composite(rgb, base, a)
            fixed = Image.composite(blended, rgb, inner)
            im = Image.merge("RGBA", (*fixed.split(), im.getchannel("A")))
        im.putalpha(self._fill_holes(ImageChops.lighter(solid, inner)))
        return im

    @staticmethod
    def _avoid_key(im):
        """투명 색상키와 똑같은 색의 픽셀을 1만큼 비껴 놓는다.

        창 투명화는 이 색을 통째로 뚫으므로, 그림 안에 우연히 같은 색이 있으면
        그 점만 배경이 비쳐 흰 점처럼 보인다(퀸시 얼굴 흰 점 사건).
        """
        from PIL import ImageChops
        kr, kg, kb = (int(TRANSPARENT[i:i + 2], 16) for i in (1, 3, 5))
        r, g, b, al = im.split()
        eq = ImageChops.multiply(
            ImageChops.multiply(r.point(lambda v: 255 if v == kr else 0),
                                g.point(lambda v: 255 if v == kg else 0)),
            b.point(lambda v: 255 if v == kb else 0))
        if not eq.getbbox():
            return im
        bump = eq.point(lambda v: 1 if v else 0)
        nb = ImageChops.add(b, bump) if kb < 255 else ImageChops.subtract(b, bump)
        return Image.merge("RGBA", (r, g, nb, al))

    @staticmethod
    def _fill_holes(solid):
        """실루엣 '안쪽'의 투명 구멍만 메운다.

        얼굴의 옅은 음영선처럼 반투명하게 그려진 내부 선은 이분화하면 구멍이
        되어, 밝은 배경에서 흰 점·선으로 비쳐 보인다(퀸시 사건). 바깥과
        이어지지 않은 투명 영역만 채우므로 실루엣 모양은 그대로 유지된다.
        """
        from PIL import ImageChops, ImageDraw
        w, h = solid.size
        pad = Image.new("L", (w + 2, h + 2), 0)
        pad.paste(solid, (1, 1))
        ImageDraw.floodfill(pad, (0, 0), 128)        # 바깥 투명 영역만 표시
        holes = pad.point(lambda v: 255 if v == 0 else 0).crop((1, 1, w + 1, h + 1))
        return ImageChops.lighter(solid, holes)

    # 뒤쪽 조각의 기본 움직임 — config의 prop_back으로 캐릭터마다 덮어쓴다
    PROP_BACK_MOTION = {
        # 느긋하게 — 빠르면 캐릭터가 안절부절못하는 것처럼 보인다.
        # 기뽀 요정 날개(back_period 1.0)보다 한참 느리게 잡았다. 그 값은
        # 날개가 작아서 괜찮았지, 큰 날개·꼬리에 그대로 쓰면 부산스럽다.
        "prop7": {"motion": "sway", "amp": 6.0, "period": 4.5,
                  "jitter": 0.25, "pivot": [0.12, 0.25]},   # 악마 꼬리
        "prop8": {"motion": "flap", "amp": 0.22, "period": 3.2,
                  "jitter": 0.3},                            # 천사 날개
    }

    def _load_prop_back(self, pick, s, pil_cache):
        """뽑힌 소품에 '몸 뒤에 그리는 짝'이 있으면 같이 읽는다.

        악마 세트는 뿔(앞)+꼬리(뒤), 천사 세트는 고리(앞)+날개(뒤)처럼
        한 소품이 몸 앞뒤로 나뉜다. PSD에서 몸체보다 아래에 둔 레이어가
        '{소품}_back'으로 뽑혀 있다.
        """
        self.has["prop_back"] = False
        name = f"{pick}_back"
        path = os.path.join(self.prop_dir, f"{name}.png")
        if name not in self._prop_layout or not os.path.exists(path):
            return
        im = Image.open(path).convert("RGBA")
        if s != 1.0:
            im = im.resize((max(1, round(im.width * s)),
                            max(1, round(im.height * s))), Image.LANCZOS)
        self.layout["prop_back"] = self._prop_layout[name]
        pil_cache["prop_back"] = im
        self.im["prop_back"] = ImageTk.PhotoImage(self._hard(im))
        self.has["prop_back"] = True
        # 기본 몸 뒤 파츠(기뽀 요정 날개)는 숨긴다 — 날개가 겹쳐 보이지 않게
        self.has["back"] = False
        cfg = dict(self.PROP_BACK_MOTION.get(pick) or {})
        cfg.update((self.cfg.get("prop_back") or {}).get(pick) or {})
        self._prop_back_cfg = cfg

    @staticmethod
    def _props_in(layout, folder):
        """layout과 실제 PNG가 둘 다 있는 소품 이름들 (자동업데이트 섞임 대비).

        '..._back'은 몸 뒤에 그리는 짝(악마 꼬리·천사 날개)이라 따로 뽑지
        않는다. 앞쪽 소품이 뽑히면 그 짝으로 같이 따라 나온다.
        """
        return sorted(n for n in layout
                      if n.startswith("prop") and n != "prop"
                      and not n.endswith("_back")
                      and os.path.exists(os.path.join(folder, f"{n}.png")))

    def _pick_prop(self):
        """이번 실행에 쓸 소품 하나를 고른다 (없으면 None).

        같은 게 연달아 나오지 않도록, 한 바퀴 다 돌 때까지 쓴 것을 빼고
        고른다. 다 쓰면 초기화하되 직전 것만 제외해 연속 중복을 막는다.
        기록은 상태 폴더에 남겨 자동 업데이트로 지워지지 않게 한다.
        """
        # 패션 슬롯에 소품이 없으면 기본 폴더 것을 쓴다 — 소품은 얼굴 위
        # 덮개라 슬롯(옷)이 바뀌어도 좌표가 같다.
        self.prop_dir, src = self.parts_dir, self.layout
        avail = self._props_in(self.layout, self.parts_dir)
        if not avail and self.parts_dir != self.dir:
            try:
                with open(os.path.join(self.dir, "layout.json"),
                          encoding="utf-8") as fp:
                    base = json.load(fp)
                hit = self._props_in(base, self.dir)
            except Exception:
                hit = []
            if hit:
                self.prop_dir, src, avail = self.dir, base, hit
        if not avail:
            return None
        self._prop_layout = src
        path = os.path.join(self.state_dir, ".props.json")
        used, last = [], None
        try:
            with open(path, encoding="utf-8") as fp:
                d = json.load(fp)
            used = [str(x) for x in (d.get("used") or []) if x in avail]
            last = d.get("last")
        except Exception:
            pass
        pool = [n for n in avail if n not in used]
        if not pool:                       # 한 바퀴 다 돎 — 직전 것만 빼고 재시작
            used = []
            pool = [n for n in avail if n != last] or avail
        pick = random.choice(pool)
        try:
            with open(path, "w", encoding="utf-8") as fp:
                json.dump({"used": used + [pick], "last": pick}, fp)
        except Exception:
            pass
        return pick

    def _load_parts(self):
        s = self.s

        # 밑그림에 완전히 덮이는 얼굴 파츠는 가장자리를 이분화하지 않는다.
        # 이분화는 투명한 배경과 닿을 때 생기는 회색 테두리를 막으려는 것인데,
        # 배경에 닿지 않는 파츠에서는 얇은 선만 잘려 나간다(속눈썹은 픽셀의
        # 1/4가 사라졌다). Tk는 아래 그림과 알파 합성을 해 주므로 그냥 둬도
        # 테두리가 지지 않는다.
        self._soft_parts = self._find_covered_parts()

        def load_pil(name):
            """파츠 원본을 표시 배율로 줄여 둔다 (이분화는 하지 않는다).

            이분화를 미리 해 두면, 몸짓이 그 계단진 그림을 다시 돌리고 늘리면서
            손상이 두 번 겹쳐 선이 뭉텅뭉텅 끊긴다. 그래서 부드러운 원본을
            들고 있다가 화면에 올리는 마지막 순간에 한 번만 이분화한다.
            들고 있는 그림 수는 그대로라 메모리는 늘지 않는다.
            """
            im = Image.open(os.path.join(self.parts_dir,
                                         f"{name}.png")).convert("RGBA")
            if s != 1.0:
                im = im.resize((max(1, round(im.width * s)),
                                max(1, round(im.height * s))), Image.LANCZOS)
            return im

        def firm(name, im):
            """화면에 바로 올릴 그림 — 배경에 닿는 파츠만 이분화한다."""
            return im if name in self._soft_parts else self._hard(im)

        self.im = {}
        self.has = {}
        pil_cache = {}
        for name in ("body_open", "pupils", "body_mask", "lashes", "hair",
                     "eyes_closed", "head", "desk", "arm_pen",
                     "smile", "pet1", "pet2", "scarf", "back"):
            # 파일과 layout 위치가 둘 다 있어야 사용 (자동업데이트 섞임 대비)
            self.has[name] = (os.path.exists(os.path.join(self.parts_dir,
                                                          f"{name}.png"))
                              and name in self.layout)
            if self.has[name]:
                pil_cache[name] = load_pil(name)
                self.im[name] = ImageTk.PhotoImage(firm(name, pil_cache[name]))

        # 소품(prop1..N) — 켤 때마다 하나만 랜덤으로. 고른 것을 "prop"으로
        # 이름 붙여 두면 overlays 순서대로 얼굴 위에 함께 그려진다.
        self.has["prop"] = False
        pick = self._pick_prop()
        if pick:
            self.layout["prop"] = self._prop_layout[pick]
            im = Image.open(os.path.join(self.prop_dir,
                                         f"{pick}.png")).convert("RGBA")
            if s != 1.0:
                im = im.resize((max(1, round(im.width * s)),
                                max(1, round(im.height * s))), Image.LANCZOS)
            # 소품도 머리 안에만 있으면 이분화하지 않는다 (안경테 계단 방지)
            covered = self._covered_by_base(
                self._prop_layout[pick],
                os.path.join(self.prop_dir, f"{pick}.png"))
            pil_cache["prop"] = im
            self.im["prop"] = ImageTk.PhotoImage(im if covered
                                                 else self._hard(im))
            self.has["prop"] = True
            self.prop_name = pick
            # 소품마다 그리는 층이 다르다 — 안경은 앞머리 아래, 머리띠는
            # 앞머리 위. PSD에서 뽑아 둔 'over'(덮개 몇 장 뒤인가)대로 끼운다.
            ov = [o for o in (self.layout.get("overlays") or []) if o != "prop"]
            over = self._prop_layout[pick].get("over")
            if over is None:
                # 옛 layout이라 정보가 없다 — 예전처럼 머리카락 앞에 둔다
                pos = ov.index("hair") if "hair" in ov else len(ov)
            else:
                pos = max(0, min(int(over), len(ov)))
            ov.insert(pos, "prop")
            self.layout["overlays"] = ov
            self._load_prop_back(pick, s, pil_cache)

        # 타이머 카드 가로 중심 = 책상 내용의 중심 (캔버스 중심이 아니라)
        self.card_cx = self.W / 2
        self._desk_top = self.H * 0.6        # 반려동물이 올라오는 기준선
        if "desk" in pil_cache:
            bb = pil_cache["desk"].split()[3].getbbox()
            if bb:
                # 책상 PNG가 캔버스 전체가 아니라 잘려 있을 수 있으므로
                # layout 위치를 더해 창 좌표로 옮긴다 (옛 캐릭터는 pos가 0,0)
                dx, dy = self.layout["desk"]["pos"]
                dx, dy = dx * s + self.ox, dy * s
                self.card_cx = dx + (bb[0] + bb[2]) / 2
                self._desk_top = dy + bb[1]

        self._build_pet_mask(pil_cache)
        self._load_hat(pil_cache)

        # 잘 때 머리를 기울이는 축 = 목 (머리 가로 중심 · 몸통 윗선)
        self._tilt_cache = {}
        self._tilt_max = 0.0
        self._tilt_base = self._tilt_base_awake = None
        self._tilt_base_smile = None
        base = "head" if self.has.get("head") else "body_open"
        base_im = pil_cache.get(base)
        hb = base_im.split()[3].getbbox() if base_im is not None else None
        hx, hy = self.layout.get(base, {}).get("pos", (0, 0))
        # 머리(없으면 몸통) 실루엣 상자 — zzZ 위치·기울임 축의 기준
        self._head_box = ((hx * s + self.ox + hb[0], hy * s + hb[1],
                           hx * s + self.ox + hb[2], hy * s + hb[3]) if hb else
                          (0, 0, self.W, self.H))
        if self.has.get("head"):
            self._neck = ((self._head_box[0] + self._head_box[2]) / 2,
                          self.layout["body_open"]["pos"][1] * s + 6)

        # 회전 손 파츠: 어깨(최상단) 앵커 기준으로 회전 — 어깨가 몸에서 안 떨어짐
        self.hop = {}
        for name in ("arm_key", "arm_right_typing", "arm_pen"):
            try:
                im = load_pil(name)
            except Exception:
                continue
            ab = im.split()[3].getbbox()
            top = ab[1]
            row = im.crop((0, top, im.width, min(top + 3, im.height))).split()[3].getbbox()
            anchor_x = (row[0] + row[2]) / 2 if row else im.width / 2
            # 회전 여유 패딩. 펜 쥔 손은 제스처에서 크게 흔드는데 파츠가
            # 길어서(펜) 끝이 많이 돌아나가므로 여유를 더 준다.
            m = max(6, round(im.height * (0.45 if name == "arm_pen" else 0.18)))
            padded = Image.new("RGBA", (im.width + 2 * m, im.height + m), (0, 0, 0, 0))
            padded.paste(im, (m, 0))
            self.hop[name] = {"pil": padded, "anchor": (anchor_x + m, top),
                              "off": (-m, 0), "cache": {}}

        # 오른팔: 늘리기용. 좌우 반전본은 박수처럼 팔이 몸 안쪽을 향해야 할 때
        # 쓴다 (원본은 바깥으로 휘어 있어 안쪽으로 모으면 어색하다).
        try:
            self.arm_pil = load_pil("arm_right")
        except Exception:
            self.arm_pil = None
        self.arm_pil_m = (ImageOps.mirror(self.arm_pil)
                          if self.arm_pil is not None else None)
        # 왼팔(arm_key)도 손끝을 원하는 자리로 보낼 수 있게 위·아래 접합점을
        # 잰다. 오른팔은 layout.json에 적혀 오지만 왼팔은 없어서 직접 잰다.
        self.arm_key_pil = None
        self._armk_anchor = None
        try:
            ki = load_pil("arm_key")
            self.arm_key_pil = ki
            self._armk_anchor = _end_anchors(ki)
        except Exception:
            pass
        self._arm_cache = {}
        self._build_notes()             # 리듬 탈 때 튀어나오는 음표
        # 펜 쥔 손을 '팔 손끝'을 축으로 돌리기 위한 판. 축을 그림 한가운데에
        # 두고 정사각형으로 만들어 두면 어느 각도로 돌려도 잘리지 않는다.
        # (손을 안 돌리면 팔만 방향이 바뀌어 손이 팔에서 떨어져 보인다.)
        self._pen_rot = None
        try:
            pi = load_pil("arm_pen")
            ar, ap = self.layout["arm_right"], self.layout["arm_pen"]
            vx = (ar["pos"][0] + ar["bottom"][0] - ap["pos"][0]) * s
            vy = (ar["pos"][1] + ar["bottom"][1] - ap["pos"][1]) * s
            R = int(math.ceil(max(math.hypot(vx - x, vy - y)
                                  for x in (0, pi.width)
                                  for y in (0, pi.height)))) + 2
            sq = Image.new("RGBA", (2 * R, 2 * R), (0, 0, 0, 0))
            sq.alpha_composite(pi, (int(round(R - vx)), int(round(R - vy))))
            self._pen_rot = {"pil": sq, "cache": {}}
        except Exception:
            self._pen_rot = None
        # 왼손 위치 미세 보정 (캔버스 px, config의 arm_key_offset)
        ko = self.cfg.get("arm_key_offset", [0, 0])
        self.arm_key_off = (ko[0] * s, ko[1] * s)
        self._pil_cache = {n: pil_cache[n] for n in pil_cache}
        self._load_pil = load_pil

        if self.has.get("head"):
            self._build_tilt_base()     # 잘 때 기울이는 머리 한 장 + 최대 각도

        self._bake_oy()                 # oy 의존 좌표 계산
        self._build_shadow_img()        # 그림자 이미지 생성

    def _load_hat(self, pil_cache):
        """축하용 고깔모자 — 머리 폭에 맞춰 줄이고 살짝 기울여 둔다."""
        path = os.path.join(self.parts_dir, "hat.png")
        if not os.path.exists(path):        # 스킨 폴더에 없으면 기본에서
            path = os.path.join(self.dir, "hat.png")
        self.hat_anchor = (0, 0)
        if not os.path.exists(path):
            self.has["hat"] = False
            return
        base = "head" if self.has.get("head") else "body_open"
        if base not in pil_cache:
            self.has["hat"] = False
            return
        bb = pil_cache[base].split()[3].getbbox()
        head_w = (bb[2] - bb[0]) if bb else self.W
        im = Image.open(path).convert("RGBA")
        k = head_w * float(self.cfg.get("hat_scale", 0.24)) / max(im.width, 1)
        im = im.resize((max(8, round(im.width * k)), max(8, round(im.height * k))),
                       Image.LANCZOS)
        im = im.rotate(14, expand=True, resample=self._resample())
        self.im["hat"] = ImageTk.PhotoImage(self._hard(im))
        self.has["hat"] = True

    TILT_PAD = 70                    # 회전 여유 (잘려나가지 않게 캔버스를 넓혀 합성)

    def _build_tilt_base(self):
        """머리+얼굴 파츠를 한 장으로 합쳐 두고, 창을 안 벗어나는 최대 각도를 구한다."""
        p = self.TILT_PAD
        layer = Image.new("RGBA", (self.W + 2 * p, self.H + 2 * p), (0, 0, 0, 0))

        def paste(name):
            x, y = self.layout[name]["pos"]
            layer.alpha_composite(self._pil_cache[name],
                                  (round(x * self.s) + p, round(y * self.s) + p))

        overlays = self.layout.get("overlays") or ["eyes_closed", "hair"]
        paste("head")
        for name in overlays:
            if name in ("body_mask", "head") or not self.has.get(name):
                continue
            paste(name)
        self._tilt_base = layer

        # 깨어 있을 때 기울이는 판 — 눈을 감기지 않고 눈동자를 넣는다.
        # 잘 때 쓰는 판에는 '눈깜빡'이 들어 있어서, 그대로 쓰면 몸짓만
        # 하면 눈을 감아 버린다. 눈동자는 기울인 동안 가운데로 고정된다.
        layer2 = Image.new("RGBA", (self.W + 2 * p, self.H + 2 * p), (0, 0, 0, 0))
        layer, self._tilt_base_awake = layer2, layer2
        paste("head")
        if self.has.get("pupils"):
            paste("pupils")
        for name in overlays:
            if name in ("body_mask", "head", "eyes_closed")                     or not self.has.get(name):
                continue
            paste(name)

        # 웃는 얼굴로 기울이는 판 — 리듬을 타는 내내 웃고 있어야 하는데,
        # 눈 뜬 판을 쓰면 고개가 기울 때마다 표정이 평소로 돌아가 깜빡인다.
        self._tilt_base_smile = None
        if self.has.get("smile"):
            layer3 = Image.new("RGBA", (self.W + 2 * p, self.H + 2 * p),
                               (0, 0, 0, 0))
            layer, self._tilt_base_smile = layer3, layer3
            paste("head")
            for name in overlays:
                if name in ("body_mask", "head", "lashes")                         or not self.has.get(name):
                    continue
                paste("smile" if name == "eyes_closed" else name)
            if "eyes_closed" not in overlays:
                paste("smile")

        self._tilt_max = 0.0
        # 실제로 돌려 보고, 창 밖으로 8px 이내로만 밀리는 최대 각도를 고른다
        for deg in (8, 7, 6, 5, 4, 3, 2):
            if abs(self._tilt_fit(self._rot_head(-deg))) <= 8:
                self._tilt_max = float(deg)
                break
        # 창 안에 들어가도 '보기에' 자연스러운 각도는 캐릭터마다 다르다.
        # 기뽀처럼 머리 밑변이 평평하고 몸과 겹치는 부분이 얇으면, 조금만
        # 기울여도 머리가 벗겨져 굴러떨어지는 것처럼 보인다(제보).
        self._tilt_max *= max(0.0, min(1.0, float(self.cfg.get("tilt_scale", 1.0))))

    def _rot_head(self, deg, mode="sleep"):
        p = self.TILT_PAD
        base = {"awake": self._tilt_base_awake,
                "smile": self._tilt_base_smile}.get(mode) or self._tilt_base
        # _neck은 화면 좌표(ox 포함)인데 합성판은 ox가 없다 — 빼고 돌린다
        return base.rotate(deg, center=(self._neck[0] - self.ox + p,
                                        self._neck[1] + p),
                           resample=self._resample())

    def _tilt_fit(self, im):
        """돌린 머리가 창 안에 들어오도록 좌우로 밀어야 할 픽셀 수."""
        p = self.TILT_PAD
        bb = im.split()[3].getbbox()
        if not bb:
            return 0
        # 그릴 때 ox만큼 오른쪽으로 밀리므로 그것까지 계산에 넣는다
        return (max(p + 2 - self.ox - bb[0], 0)
                - max(bb[2] + self.ox - (p + self.W - 2), 0))

    def _sleep_head(self, deg, mode="sleep"):
        """기울어진 머리 — (이미지, 창 안으로 미는 보정값), 1도 단위 캐시."""
        key = (round(deg), mode)
        hit = self._tilt_cache.get(key)
        if hit is not None:
            return hit
        if len(self._tilt_cache) > 60:
            self._tilt_cache.clear()
        layer = self._rot_head(key[0], mode)
        dx = max(-12, min(12, self._tilt_fit(layer)))
        hit = (ImageTk.PhotoImage(self._hard(layer)), dx)
        self._tilt_cache[key] = hit
        return hit

    def _tilt_xy(self, x, y, deg):
        """목을 축으로 deg만큼 돈 뒤의 좌표 (콧방울 따라가기용)."""
        a = math.radians(deg)
        nx, ny = self._neck
        dx, dy = x - nx, y - ny
        return (nx + dx * math.cos(a) - dy * math.sin(a),
                ny + dx * math.sin(a) + dy * math.cos(a))

    def _draw_snot(self, now, yo, deg, tdx=0):
        """자는 동안 코에서 부풀었다 꺼지는 콧방울."""
        nose = self.cfg.get("nose")
        if not nose:
            return
        t = now % 5.2
        if t < 3.8:
            r = 2.0 + 11.0 * (t / 3.8) ** 1.6
        elif t < 4.05:
            r = 13.0 * (1 - (t - 3.8) / 0.25)      # 픽 하고 꺼짐
        else:
            return
        if r < 1.5:
            return
        x, y = nose[0] * self.s + self.ox, nose[1] * self.s
        x, y = self._tilt_xy(x, y, -deg)           # 캔버스 좌표는 회전 방향 반대
        x += tdx
        y += self.oy + yo
        c = self.canvas
        cx, cy = x + r * 0.15, y + r * 0.85
        c.create_oval(cx - r, cy - r, cx + r, cy + r,
                      fill="#dfeeff", outline="#8dbfe4", width=2)
        c.create_oval(cx - r * 0.55, cy - r * 0.6, cx - r * 0.05, cy - r * 0.1,
                      fill="#ffffff", outline="")

    def _build_pet_mask(self, pil_cache):
        """반려동물이 '책상 뒤'에 있도록, 열마다 책상 윗선 위쪽만 남기는 마스크."""
        self._pet_cache = {}
        self._pet_hide = {}
        self.pet_cast = []
        if not (self.has.get("pet1") or self.has.get("pet2")):
            self._pet_mask = None
            return
        if "desk" not in pil_cache:
            self._pet_mask = None
            return
        desk = pil_cache["desk"]
        W, H = desk.size
        alpha = desk.split()[3].point(lambda v: 255 if v > 40 else 0)
        tops = []
        for x in range(W):                       # 열별 책상 최상단 행
            bb = alpha.crop((x, 0, x + 1, H)).getbbox()
            tops.append(bb[1] if bb else None)
        last = H
        for x in range(W):                       # 책상이 없는 열은 이웃 값으로
            if tops[x] is None:
                tops[x] = last
            else:
                last = tops[x]
        last = H
        for x in range(W - 1, -1, -1):
            if tops[x] == H:
                tops[x] = last
            else:
                last = tops[x]
        mask = Image.new("L", (W, H), 0)
        col = Image.new("L", (1, H), 255)
        for x, t in enumerate(tops):
            if t > 0:
                mask.paste(col.crop((0, 0, 1, t)), (x, 0))
        self._pet_mask = mask
        self._pet_xy = {}
        k = float(self.cfg.get("pet_scale", 1.3))
        for name in ("pet1", "pet2"):
            if not self.has.get(name):
                continue
            small = pil_cache[name]
            rot = float(self.cfg.get("pet_rot", 0))
            if k != 1.0 or rot:                  # 원본에서 다시 줄여야 안 뭉갠다
                src = Image.open(os.path.join(self.parts_dir,
                                              f"{name}.png")).convert("RGBA")
                big = src.resize((max(1, round(src.width * self.s * k)),
                                  max(1, round(src.height * self.s * k))),
                                 Image.LANCZOS)
                if rot:                          # 캐릭터 뒤에서 안 가리게 기울이기
                    big = big.rotate(rot, expand=True, resample=self._resample())
                bb = big.split()[3].getbbox()    # 회전으로 생긴 빈 여백은 잘라낸다
                if bb:
                    big = big.crop(bb)
                pil_cache[name] = big = self._hard(big)
            else:
                big = small
            px, py = self.layout[name]["pos"]
            px, py = px * self.s + self.ox, py * self.s
            # 원래 실루엣의 밑변 중심을 기준으로 커지고 기울어지게
            sb = small.split()[3].getbbox() or (0, 0, small.width, small.height)
            ax, ay = px + (sb[0] + sb[2]) / 2, py + sb[3]
            px = round(ax - big.width / 2) + int(self.cfg.get("pet_dx", 0))
            py = round(ay - big.height)
            px = max(2, min(px, self.W - big.width - 2))   # 창 밖으로 안 나가게
            self._pet_xy[name] = (px, py)
            # 모든 열에서 책상 윗선 아래로 내려가면 완전히 사라진다
            need = max(tops[min(max(px + j, 0), W - 1)]
                       for j in range(big.width)) - py
            self._pet_hide[name] = max(need + 4, 10)


    def _timer_oy(self):
        """타이머 카드가 차지하는 캐릭터 위 여백."""
        if not self.timer_on:
            return 0
        if self.has_clock:
            return OY_CLOCK_OPEN if self.clock_open else OY_CLOCK_COMPACT
        extra = int(self.cfg.get("card_top", 22)) - 22        # 장식 여유 (토끼 귀)
        return TIMER_H + (26 if self.cfg.get("fun") else 0) + extra

    def _bake_oy(self):
        """oy(카드 높이)에 의존하는 좌표들 — 시계 토글로 oy가 바뀌면 다시 부른다."""
        s = self.s
        ar = self.layout["arm_right"]
        ax, ay = ar["pos"]
        self.arm_top = ((ax + ar["top"][0]) * s + self.ox,
                        (ay + ar["top"][1]) * s + self.oy)
        self.arm_bottom = ((ax + ar["bottom"][0]) * s + self.ox,
                           (ay + ar["bottom"][1]) * s + self.oy)
        self._arm_nat = (self.arm_bottom[0] - self.arm_top[0],
                         self.arm_bottom[1] - self.arm_top[1])
        # 왼팔(반전 재활용)의 어깨와 손끝. 어깨는 오른쪽 어깨를 몸통 한가운데
        # 기준으로 접어 넘긴 자리, 손끝은 왼손 파츠가 팔에 붙는 지점이다.
        bo = self.layout["body_open"]
        mid = (bo["pos"][0] + bo["size"][0] / 2) * s + self.ox
        self.body_mid_x = mid
        # 왼팔(arm_key)의 어깨와 손끝 — 그림에서 직접 잰 접합점을 화면 좌표로.
        if self._armk_anchor is not None:
            kx, ky = self.layout["arm_key"]["pos"]
            bx = kx * s + self.ox + self.arm_key_off[0]
            by = ky * s + self.oy + self.arm_key_off[1]
            (tx, ty), (ex, ey) = self._armk_anchor
            self.armk_top = (bx + tx, by + ty)
            self.armk_bottom = (bx + ex, by + ey)
        else:
            self.armk_top = (2 * mid - self.arm_top[0], self.arm_top[1])
            self.armk_bottom = (2 * mid - self.arm_bottom[0], self.arm_bottom[1])
        # 늘여 그릴 팔 그림과 그 기준 벡터. 기준이 0에 가까우면 늘이기 배율이
        # 폭발해 얼굴을 가로지르는 흰 막대가 되므로 _stretched_arm에서 막는다.
        nk = (self.armk_bottom[0] - self.armk_top[0],
              self.armk_bottom[1] - self.armk_top[1])
        self._arm_src = {}
        if self.arm_pil is not None:
            at = (ar["top"][0] * s, ar["top"][1] * s)
            ab = (ar["bottom"][0] * s, ar["bottom"][1] * s)
            w = self.arm_pil.width
            self._arm_src["r"] = (self.arm_pil, self._arm_nat, at, ab)
            self._arm_src["rm"] = (self.arm_pil_m,
                                   (-self._arm_nat[0], self._arm_nat[1]),
                                   (w - at[0], at[1]), (w - ab[0], ab[1]))
        if self.arm_key_pil is not None and self._armk_anchor is not None:
            self._arm_src["l"] = (self.arm_key_pil, nk,
                                  self._armk_anchor[0], self._armk_anchor[1])
        px, py = self.layout["arm_pen"]["pos"]
        tx, ty = self.cfg.get("pen_tip", self.layout["arm_pen"]["pen_tip"])
        self.pen_base_tip = ((px + tx) * s + self.ox, (py + ty) * s + self.oy)
        self.quad = [(x * s + self.ox, y * s + self.oy)
                     for x, y in self._quad_src]
        blink = self.cfg.get("blink")
        self.blink_cfg = None
        if blink and self.has["body_mask"]:
            r = blink["rect"]
            self.blink_cfg = ([r[0] * s + self.ox, r[1] * s + self.oy,
                               r[2] * s + self.ox, r[3] * s + self.oy],
                              blink["color"])

    def _build_shadow_img(self):
        """캐릭터+카드 실루엣을 흐려 만든 반투명 그림자 이미지.

        가장자리 파츠(귀 등)의 그림자가 잘리지 않도록 여백(P)을 두고 그린다.
        """
        self.shadow_img = self.shadow_img_type = None
        if not self.us.get("shadow", True):
            return
        for typing in (False, True):
            self._compose_shadow(typing)
        self._shadow_base = self.shadow_img
        self._shadow_typing = False

    def _compose_shadow(self, typing):
        """그림자 실루엣 한 벌. typing이면 펜 손 대신 타자 팔로 그린다."""
        from PIL import ImageDraw, ImageFilter
        P = SHADOW_PAD
        comp = Image.new("RGBA", (self.W + 2 * P, self.H + 2 * P), (0, 0, 0, 0))
        parts = ["body_open", "scarf", "lashes", "hair", "head", "desk"]
        if not typing:
            parts.append("arm_pen")
        for name in parts:
            if name in self._pil_cache:
                x, y = self._pos(name)
                comp.alpha_composite(self._pil_cache[name], (round(x) + P, round(y) + P))
        arms = ["arm_key", "arm_right_typing" if typing else "arm_right"]
        for name in arms:
            try:
                im = self._load_pil(name)
            except Exception:
                continue
            x, y = self._pos(name)
            if name == "arm_key":
                x += self.arm_key_off[0]
                y += self.arm_key_off[1]
            comp.alpha_composite(im, (round(x) + P, round(y) + P))
        if self.timer_on:
            d = ImageDraw.Draw(comp)
            cg = self._card_geom()
            cx0, cy0 = cg["x0"] + P, cg["y0"] + P
            cx1, cy1 = cg["x1"] + P, cg["y1"] + P
            # 카드 위 장식의 실루엣도 함께 — 안 맞으면 리본을 달아도 귀
            # 그림자가 진다. _draw_deco와 모양을 맞춰 둘 것.
            deco = self.card.get("deco")
            mx = (cx0 + cx1) / 2
            if deco == "ribbon":                   # 사가: 리본 실루엣
                for sign in (-1, 1):
                    d.polygon([(mx, cy0 - 1), (mx + 17 * sign, cy0 - 14),
                               (mx + 19 * sign, cy0 + 1), (mx + 15 * sign, cy0 + 6)],
                              fill=(0, 0, 0, 255))
                d.ellipse([mx - 5, cy0 - 6, mx + 5, cy0 + 4], fill=(0, 0, 0, 255))
            elif deco == "sprout":                 # 기뽀: 새싹 실루엣
                d.line([(mx, cy0 + 6), (mx, cy0 - 12)], fill=(0, 0, 0, 255), width=3)
                for sign in (-1, 1):
                    d.polygon([(mx, cy0 - 9), (mx + 8 * sign, cy0 - 18),
                               (mx + 15 * sign, cy0 - 10), (mx + 6 * sign, cy0 - 4)],
                              fill=(0, 0, 0, 255))
            elif deco == "scarf":                  # 퀸시: 목도리 띠 (귀 없음)
                d.rounded_rectangle([cx0 + 14, cy0 - 15, cx1 - 14, cy0 + 7],
                                    radius=9, fill=(0, 0, 0, 255))
            else:                                  # 귀 달린 캐릭터들
                for ex in (cx0 + 26, cx1 - 26):
                    d.ellipse([ex - 12, cy0 - 17, ex + 12, cy0 + 7],
                              fill=(0, 0, 0, 255))
            d.rounded_rectangle([cx0, cy0, cx1, cy1], radius=16, fill=(0, 0, 0, 255))
        a = comp.getchannel("A").filter(ImageFilter.GaussianBlur(7))
        a = a.point(lambda v: int(v * 0.30))
        black = Image.new("RGB", comp.size, (0, 0, 0))
        img = Image.merge("RGBA", (*black.split(), a))
        if typing:
            self.shadow_img_type = img
        else:
            self.shadow_img = img

    def _card_geom(self):
        """현재 타이머 카드의 위치·크기. 시계 펼침이면 세로 직사각형."""
        if self.has_clock and self.clock_open:
            w, h = 148, 150           # 세로가 살짝 더 긴 직사각형
        elif self.has_clock:
            w, h = 196, 40
        else:
            w, h = 200, (88 if self.cfg.get("fun") else 62)
        x0 = getattr(self, "card_cx", self.W / 2) - w / 2
        # 창 밖으로 나가지 않게 — 책상이 한쪽으로 치우친 캐릭터도 안 잘리게
        x0 = max(3.0, min(x0, self.W - w - 3.0)) if self.W >= w + 6 else x0
        y0 = float(self.cfg.get("card_top", 22))
        return {"x0": x0, "y0": y0, "x1": x0 + w, "y1": y0 + h, "w": w, "h": h}

    def _resample(self):
        """돌리고 늘릴 때 쓰는 보간.

        예전에는 이분화한 그림을 다시 돌렸기 때문에 NEAREST를 썼다(어차피
        계단이니 빠른 쪽으로). 지금은 부드러운 원본에서 돌린 뒤 마지막에
        이분화하므로, 여기서 부드럽게 보간해야 선이 살아난다.
        """
        return Image.BICUBIC

    def _draw_back(self, now, yo):
        """기본 몸 뒤 파츠 (사가 양갈래·기뽀 요정 날개)."""
        self._back_anim("back", {
            "motion": self.cfg.get("back_motion"),
            "amp": self.cfg.get("back_amp", 1.0),
            "period": self.cfg.get("back_period", 2.6),
            "jitter": self.cfg.get("back_jitter", 0.0),
            "pivot": self.cfg.get("back_pivot"),
        }, now, yo)

    def _draw_prop_back(self, now, yo):
        """뽑힌 소품의 몸 뒤 조각 (악마 꼬리·천사 날개)."""
        self._back_anim("prop_back", self._prop_back_cfg, now, yo)

    def _back_anim(self, name, mo, now, yo):
        """몸 뒤 파츠 — 설정대로 살짝 움직인다.

          sway : 붙는 자리를 축으로 좌우로 천천히 흔들림 (양갈래·꼬리)
          flap : 가로로 오므렸다 폈다 (날갯짓)
          없음 : 그냥 붙어만 있음

        프레임마다 이미지를 새로 만들면 메모리가 계속 늘어나므로(옛 팔 사고),
        움직임을 정해진 칸으로 끊어 캐시한다. 칸 수만큼만 이미지가 생긴다.
        기본 날개와 소품 날개가 함께 있을 수 있으므로 박자는 이름별로 든다.
        """
        x, y = self._pos(name)
        mode = mo.get("motion")
        if not mode:
            self._put(name, x, y + yo)
            return
        amp = float(mo.get("amp", 1.0))
        STEPS = 12                       # 한 주기를 12칸으로 — 캐시가 12장이면 끝
        st = self._back_st.get(name)
        if st is None:
            st = self._back_st[name] = {
                "phase": 0.0, "last": 0.0,
                "period": float(mo.get("period", 2.6))}
        # 위상을 직접 굴린다 — 한 번 왕복할 때마다 다음 주기를 새로 뽑을 수 있게
        # (시계에서 바로 계산하면 속도를 바꿀 수 없어 날갯짓이 기계적으로 보인다)
        dt = 0.0 if st["last"] <= 0 else min(now - st["last"], 0.2)
        st["last"] = now
        st["phase"] += dt / max(st["period"], 0.15)
        if st["phase"] >= 1.0:
            st["phase"] -= int(st["phase"])
            st["period"] = self._new_back_period(mo)
        k = int(st["phase"] * STEPS) % STEPS
        got = self._back_frame(name, mode, k, STEPS, amp, mo)
        if got is None:
            self._put(name, x, y + yo)
            return
        # 여백(pad)만큼 키운 판에 그려 두었으니 그만큼 되돌려 붙인다.
        # 이렇게 해야 회전축이 픽셀 그대로 고정된다 — 꼬리 연결부가 몸 뒤에
        # 숨어 있으려면 축이 미끄러지면 안 된다.
        img, pad = got
        self.canvas.create_image(x - pad, y - pad + yo, image=img, anchor="nw")

    @staticmethod
    def _new_back_period(mo):
        """다음 한 번의 왕복에 걸릴 시간. jitter가 있으면 매번 흔들어
        뽑는다 — 새가 파닥이듯 빨라졌다 느려졌다 하게."""
        base = float(mo.get("period", 2.6))
        j = float(mo.get("jitter", 0.0) or 0.0)
        if j <= 0:
            return base
        return base * random.uniform(max(0.15, 1.0 - j), 1.0 + j)

    def _back_frame(self, name, mode, k, steps, amp, mo):
        key = (name, mode, k)
        hit = self._back_cache.get(key)
        if hit is not None:
            return hit
        pil = self._pil_cache.get(name)
        if pil is None:
            return None
        t = math.sin(2 * math.pi * k / steps)
        pad = 0
        if mode == "sway":
            # 붙는 자리를 축으로 — 멀어질수록 크게 흔들린다. 꼬리처럼 축이
            # 한쪽에 치우친 파츠는 pivot으로 옮긴다 (그림 크기 대비 비율).
            px, py = (mo.get("pivot") or (0.5, 0.12))[:2]
            cx, cy = pil.width * float(px), pil.height * float(py)
            # expand=True로 돌리면 판이 커지면서 축이 어디로 갔는지 알기
            # 어려워, 그리는 쪽에서 중심을 어림잡게 된다. 그러면 꼬리
            # 연결부가 몸 밖으로 밀려 나온다. 대신 미리 여백을 둔 판에
            # expand 없이 돌려서 축을 픽셀 그대로 붙잡는다.
            far = max(math.hypot(dx, dy) for dx, dy in
                      ((0 - cx, 0 - cy), (pil.width - cx, 0 - cy),
                       (0 - cx, pil.height - cy),
                       (pil.width - cx, pil.height - cy)))
            pad = int(math.ceil(far * 2 * math.sin(math.radians(abs(amp)) / 2))) + 2
            base = Image.new("RGBA", (pil.width + 2 * pad, pil.height + 2 * pad),
                             (0, 0, 0, 0))
            base.alpha_composite(pil, (pad, pad))
            im = base.rotate(t * amp, center=(cx + pad, cy + pad),
                             resample=self._resample(), expand=False)
        elif mode == "flap":
            # 가로만 줄였다 늘렸다 — 좌우 날개가 함께 접혔다 펴지는 느낌
            f = 1.0 - (1.0 - math.cos(2 * math.pi * k / steps)) * 0.5 * amp
            w = max(1, int(round(pil.width * f)))
            im = Image.new("RGBA", pil.size, (0, 0, 0, 0))
            im.alpha_composite(pil.resize((w, pil.height), Image.LANCZOS),
                               ((pil.width - w) // 2, 0))
        else:
            return None
        if len(self._back_cache) > 40:
            self._back_cache.clear()
        hit = (ImageTk.PhotoImage(self._hard(im)), pad)
        self._back_cache[key] = hit
        return hit

    def _rotated_hop(self, name, deg):
        """손 파츠를 어깨 앵커 기준으로 회전한 이미지 (1도 단위 캐시)."""
        h = self.hop[name]
        key = round(deg)
        if key not in h["cache"]:
            if len(h["cache"]) > 60:
                h["cache"].clear()
            im = h["pil"].rotate(deg, center=h["anchor"],
                                 resample=self._resample(), expand=False)
            h["cache"][key] = ImageTk.PhotoImage(self._hard(im))
        return h["cache"][key]

    # ── 타자 소리 ─────────────────────────────────────────────────────────
    def _list_packs(self):
        """타자 소리 팩 목록. 캐릭터 sounds/ + 공용 '타이핑 음원/' 폴더를 함께 스캔.

        사용자가 ena-mascot/타이핑 음원/ 에 (압축 푼) Mechvibes 팩 폴더를 넣으면
        자동으로 목록에 추가된다. pack 이름 → 폴더 경로를 self._pack_paths에 저장.
        """
        self._pack_paths = {}
        for base in (os.path.join(self.dir, "sounds"),
                     os.path.join(HERE, "타이핑 음원")):
            if not os.path.isdir(base):
                continue
            for d in os.listdir(base):
                p = os.path.join(base, d)
                if d != "pen" and os.path.exists(os.path.join(p, "config.json")):
                    self._pack_paths.setdefault(d, p)   # 먼저 찾은 것 우선
        return sorted(self._pack_paths)

    def _init_sound(self):
        if self.sndpack is not None:
            try:
                self.sndpack.close()
            except Exception:
                pass
            self.sndpack = None
        if self.pensnd is not None:
            try:                            # 그레인은 close로 짧은 클립까지 회수
                getattr(self.pensnd, "close", self.pensnd.stop)()
            except Exception:
                pass
            self.pensnd = None
        if self.pokesnd is not None:
            try:
                self.pokesnd.close()
            except Exception:
                pass
            self.pokesnd = None
        self._pen_playing = False
        self._pen_release_t = None
        if not (self.us.get("sound", True) and self.sound_packs):
            return
        name = str(self.us.get("sound_pack") or "")
        if name not in self.sound_packs:
            name = self.sound_packs[0]
        pack_dir = getattr(self, "_pack_paths", {}).get(
            name, os.path.join(self.dir, "sounds", name))
        try:
            self.sndpack = SoundPack(
                pack_dir, volume=float(self.us.get("sound_volume", 60)))
        except Exception:
            self.sndpack = None
        pen_dir = os.path.join(self.dir, "sounds", "pen")
        if os.path.isdir(pen_dir):
            vol = float(self.us.get("pen_volume", 30))
            # pen_grain(도로롱 전용): 알갱이 방식. 실패하면 원샷으로 폴백.
            use_grain = bool(self.cfg.get("pen_grain")) and not IS_MAC
            try:
                self.pensnd = (PenGrainSound(pen_dir, volume=vol) if use_grain
                               else PenSound(pen_dir, volume=vol))
            except Exception:
                try:
                    self.pensnd = PenSound(pen_dir, volume=vol)
                except Exception:
                    self.pensnd = None
        self._pen_grain = isinstance(self.pensnd, PenGrainSound)
        poke_dir = os.path.join(self.dir, "sounds", "poke")
        if os.path.isdir(poke_dir):
            try:
                self.pokesnd = PokeSound(
                    poke_dir, volume=float(self.us.get("poke_volume", 40)))
            except Exception:
                self.pokesnd = None

    # ── 입력 콜백 ─────────────────────────────────────────────────────────
    def _on_key(self, key):
        self.key_events += 1
        now = time.time()
        k = str(key)
        first = k not in self._held           # 꾹 누름(자동 반복)은 최초만
        self._held.add(k)
        # 투어박스 등 다이얼: 같은 키를 사람 타이핑보다 빠르게(90ms 이내) 연타 →
        # 소리 억제 (브러시 크기·화면 회전 돌릴 때 키보드 소리 안 나게)
        dial = (now - self._key_times.get(k, 0)) < 0.09
        self._key_times[k] = now
        if first and not dial:
            self.stat["keys"] = self.stat.get("keys", 0) + 1
        sp = self.sndpack
        if first and not dial and sp is not None:
            try:
                sp.play(key, self._scan_code(key))
            except Exception:
                pass

    def _scan_code(self, key):
        """누른 키의 PS/2 스캔코드 — 사운드 팩의 defines가 쓰는 번호.

        확장키(방향키 등)는 Mechvibes와 같게 3584를 더한 번호로 맞춘다.
        """
        if not IS_WIN:
            return None
        vk = getattr(key, "vk", None)
        if vk is None:
            vk = getattr(getattr(key, "value", None), "vk", None)
        if not vk:
            ch = getattr(key, "char", None)   # vk가 없으면 글자로 되짚는다
            if not (isinstance(ch, str) and len(ch) == 1):
                return None
            try:
                fn = ctypes.windll.user32.VkKeyScanW
                fn.argtypes = [ctypes.c_wchar]   # 코드가 아니라 글자를 넘긴다
                fn.restype = ctypes.c_short      # 못 찾으면 -1
                got = fn(ch)
            except Exception:
                return None
            if got == -1:
                return None
            vk = got & 0xFF
        try:
            sc = ctypes.windll.user32.MapVirtualKeyW(int(vk), 4)  # VK_TO_VSC_EX
        except Exception:
            return None
        if not sc:
            return None
        return 3584 + (sc & 0xFF) if sc > 0xFF else sc

    def _poll_mac_input(self):
        """맥: 리스너 콜백 대신 카운터 변화를 읽어 같은 상태를 만든다."""
        mi = self._macin
        if mi is None:
            return
        dk, dm, pressed = mi.read()
        now = time.time()
        if dk:
            self.key_events += dk
            self.stat["keys"] = self.stat.get("keys", 0) + dk
            sp = self.sndpack
            if sp is not None:
                try:
                    sp.play(self.key_events)      # 한 프레임에 한 번만
                except Exception:
                    pass
        if dm:
            self.last_pointer = now
            if self.mouse_pressed:
                self.last_drag = now
        if pressed != self.mouse_pressed:
            self.mouse_pressed = pressed
            self.last_pointer = now
            if not pressed:
                self._new_stroke = True

    def _on_key_release(self, key):
        self._held.discard(str(key))

    def _on_click(self, x, y, _button, pressed):
        self.mouse_pressed = pressed
        now = time.time()
        self.last_pointer = now
        if not pressed:
            self._new_stroke = True
        # 펜 소리는 여기서 바로 판정한다 — 그리기 루프를 기다리면 늦다
        if self._pen_grain and self.pensnd is not None:
            try:
                if pressed:
                    self.pensnd.pen_down(x, y, now)
                else:
                    self.pensnd.pen_up(now)
            except Exception:
                pass

    def _on_move(self, x, y):
        now = time.time()
        self.last_pointer = now
        if self.mouse_pressed:
            self.last_drag = now
        if self._pen_grain and self.pensnd is not None:
            try:
                self.pensnd.pen_move(x, y, now)
            except Exception:
                pass

    def _on_press(self, e):
        self._press = (e.x, e.y, e.x_root, e.y_root)
        self._dragged = False

    def _on_drag(self, e):
        if self._press is None:
            return
        px, py, prx, pry = self._press
        if not self._dragged and abs(e.x_root - prx) + abs(e.y_root - pry) < 4:
            return
        self._dragged = True
        self.root.geometry(f"+{e.x_root - px}+{e.y_root - py}")

    def _on_release(self, e):
        if self._dragged:
            self._safe("win_pos", self._save_win_pos)
        if self._press is not None and not self._dragged:
            px, py, _, _ = self._press
            g = self._card_geom()
            on_card = (g["x0"] <= px <= g["x1"] and g["y0"] - 17 <= py <= g["y1"])
            btn = getattr(self, "_end_btn", None)
            if self.fun and btn and btn[0] <= px <= btn[2] and btn[1] <= py <= btn[3]:
                self._end_workday()                    # 작업 종료 버튼
            elif self.has_clock and on_card:
                self._toggle_clock()
            elif self.can_talk and not on_card and py > self.oy:
                self._on_poke()                        # 캐릭터를 콕 찌름
        self._press = None

    def _todo_load(self):
        try:
            with open(self.todo_path, encoding="utf-8") as fp:
                data = json.load(fp)
            items = data if isinstance(data, list) else data.get("items", [])
            self.todos = [str(t)[:200] for t in items if str(t).strip()][:20]
            if isinstance(data, dict):
                p = data.get("pos")
                if isinstance(p, (list, tuple)) and len(p) == 2:
                    self.todo_pos = (int(p[0]), int(p[1]))
                self.todo_flip = bool(data.get("flip"))
                self.todo_zoom = TodoPanel._near_zoom(data.get("zoom", 100))
        except Exception:
            self.todos = []

    def _todo_save(self):
        try:
            with open(self.todo_path, "w", encoding="utf-8") as fp:
                json.dump({"items": self.todos, "pos": self.todo_pos,
                           "flip": self.todo_flip, "zoom": self.todo_zoom},
                          fp, ensure_ascii=False)
        except Exception:
            pass

    def _todo_upload(self, text):
        """완료한 할 일을 워크스페이스 '오늘의 할일'에 완료 상태로 올린다.

        여기서 직접 서버에 보내지 않고 줄 단위로 파일에 적어 둔다. 기존
        타이머가 읽어 올려 주므로, 지금 꺼져 있어도 다음에 켜질 때 올라간다.
        날짜(작업일 경계 06:00) 계산도 그쪽 기준 하나로 통일한다.
        """
        text = str(text).strip()
        if not (text and self.ws_path and self.cfg.get("workspace_todo")):
            return
        path = os.path.join(os.path.dirname(self.ws_path), ".mascot_todo")
        with open(path, "a", encoding="utf-8") as fp:
            fp.write(json.dumps({"goal": text[:500], "ts": time.time()},
                                ensure_ascii=False) + os.linesep)

    def _todo_zoomed(self, pct):
        """할 일 목록 배율을 기억하고 바로 다시 그린다."""
        # 자리는 저장하지 않는다 — 직접 옮긴 적이 없다면 다음에 켤 때도
        # 그때의 폭에 맞춰 캐릭터 옆에 붙는 게 맞다.
        self.todo_zoom = int(pct)
        self._todo_save()
        self._last_pos = None                # 다음 틱에 위치 재적용
        self._todo_refresh()

    def _todo_flipped(self, flip):
        """꼬리 방향을 기억한다 — 패널을 캐릭터 오른쪽에 두는 사람도 있다."""
        self.todo_flip = bool(flip)
        self._todo_save()
        self._todo_refresh()

    def _todo_moved(self, x, y):
        """패널을 끌어서 옮기면 본체 기준 상대 위치로 기억한다."""
        self.todo_pos = (int(x - self.root.winfo_rootx()),
                         int(y - self.root.winfo_rooty()))
        if self.todo_panel is not None:
            self.todo_panel.offset = self.todo_pos
            self.todo_panel._moved_by_user = True
        self._last_pos = None                # 다음 틱에 위치 재적용
        self._todo_save()

    def _due_tick(self):
        """마감 말풍선을 캐릭터 옆에 붙여 두고, 날짜가 바뀌면 다시 그린다."""
        if self.due_panel is None:
            return
        if time.strftime("%Y-%m-%d") != self._due_shown:
            self._due_refresh()
            return
        self.due_panel.place(self.root.winfo_rootx(), self.root.winfo_rooty())

    def _todo_refresh(self):
        if self.todo_panel is None:
            return
        self.todo_panel.render(self.todos)
        self.todo_panel.place(self.root.winfo_rootx(), self.root.winfo_rooty())

    def _todo_done(self, idx):
        """우클릭 > 완료 — 그 할 일이 사라지고 캐릭터가 축하해 준다."""
        if not (0 <= idx < len(self.todos)):
            return
        done_text = self.todos[idx]
        del self.todos[idx]
        self._todo_save()
        self._safe("todo_up", self._todo_upload, done_text)
        self._todo_refresh()
        now = time.time()
        self.smile_until = now + 4.0        # 웃는 표정 (파츠 없으면 그냥 넘어감)
        self.click_bounce = now + 0.45      # 콩 하고 튐
        self.squash_until = now + 0.12
        self._gest_start("clap", force=True)
        left = len(self.todos)
        msg = ("할 일 다 끝냈어요!" if left == 0
               else random.choice(["하나 끝!", "잘했어요!", "좋아요!",
                                   f"{left}개 남았어요!"]))
        self._say(msg, 3.0)
        self._safe("todo_pop", self._burst, 18)
        for _ in range(2):                  # 잘했다는 하트
            self._safe("fx", self._spawn_note, now, "heart")

    def _todo_delete(self, idx):
        """우클릭 > 삭제 — 목록에서만 뺀다.

        '완료'와 다르다. 축하도 없고 끝낸 일로 기록에도 올리지 않는다
        (잘못 적었거나 안 하기로 한 일을 지우는 용도).
        """
        if not (0 <= idx < len(self.todos)):
            return
        del self.todos[idx]
        self._todo_save()
        self._todo_refresh()

    def _todo_edit(self, idx):
        """우클릭 > 수정 — 그 할 일의 글을 고친다."""
        if 0 <= idx < len(self.todos):
            self.add_todo(edit=idx)

    def add_todo(self, edit=None):
        """할 일 입력 창 — 엔터로 추가, Esc로 닫기. 연달아 여러 개 적을 수 있다.

        edit에 번호를 주면 그 할 일을 고치는 창이 된다(엔터 한 번으로 끝).
        """
        if getattr(self, "_todo_win", None) is not None                 and self._todo_win.winfo_exists():
            self._todo_win.destroy()        # 수정 창을 새로 열 수 있게 닫는다
        cd = self.card
        u = self._ui
        W, H = u(300), u(118)
        win = tk.Toplevel(self.root)
        self._todo_win = win
        win.title("할 일 수정" if edit is not None else "할 일 추가")
        win.attributes("-topmost", True)
        win.resizable(False, False)
        win.configure(bg=cd["panel"])
        cv = tk.Canvas(win, width=W, height=H, bg=cd["panel"],
                       highlightthickness=0)
        cv.pack()

        def rr(x0, y0, x1, y1, r, **kw):
            pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1,
                   x1 - r, y1, x0 + r, y1, x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]
            return cv.create_polygon(pts, smooth=True, **kw)

        rr(u(14), u(12), W - u(14), u(44), u(12), fill=cd["soft"],
           outline=cd["border"], width=2)
        cv.create_text(W / 2, u(28),
                       text="이렇게 바꿀까요?" if edit is not None else "무엇을 할까요?",
                       font=self._uf(10, True), fill=cd["text"])
        var = tk.StringVar(value=self.todos[edit] if edit is not None
                           and edit < len(self.todos) else "")
        ent = tk.Entry(win, textvariable=var, font=self._uf(10),
                       relief="flat", bg="#ffffff", fg=cd["text"],
                       highlightthickness=1, highlightbackground=cd["border"],
                       highlightcolor=cd["fill"])
        cv.create_window(u(20), u(56), anchor="nw", window=ent,
                         width=W - u(40), height=u(26))
        cv.create_text(W / 2, u(100),
                       text=("엔터로 저장 · Esc로 취소" if edit is not None
                             else "엔터로 추가 · Esc로 닫기"),
                       font=self._uf(8), fill=cd["sub"])

        def commit(_e=None):
            text = var.get().strip()
            if edit is not None:                 # 수정: 한 번 고치고 닫는다
                if text and edit < len(self.todos):
                    self.todos[edit] = text[:200]
                    self._todo_save()
                    self._todo_refresh()
                win.destroy()
                return
            if text:
                self.todos.append(text[:200])
                del self.todos[20:]
                self._todo_save()
                self._todo_refresh()
                var.set("")
            else:
                win.destroy()

        ent.bind("<Return>", commit)
        win.bind("<Escape>", lambda _e: win.destroy())
        if edit is not None:
            ent.select_range(0, "end")       # 바로 고쳐 쓸 수 있게 전체 선택
        win.update_idletasks()
        sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
        px = min(max(self.root.winfo_rootx() - 40, 10), max(sw - W - 10, 10))
        py = min(max(self.root.winfo_rooty() - 20, 10), max(sh - H - 60, 10))
        win.geometry(f"+{int(px)}+{int(py)}")
        ent.focus_force()

    def _on_poke(self):
        """캐릭터 클릭 반응 — 콩 튀고 한마디. (반응 파츠는 나중에 교체 가능)"""
        now = time.time()
        self.click_bounce = now + 0.45
        self.squash_until = now + 0.12
        self._panel_z = 0.0          # 눌러서 캐릭터가 앞으로 나왔다 — 바로 되돌린다
        if self.pokesnd is not None:
            try:
                self.pokesnd.play()
            except Exception:
                pass
        if self.stretch_pending:          # 스트레칭 알림을 끄는 클릭
            self._stretch_done(now)
            return
        # 세 번에 한 번쯤은 몸으로도 반응한다 (매번 하면 금방 질린다)
        if random.random() < 0.35:
            self._gest_start(random.choice(("wave", "nod", "shake")))
        self._say(self._pick_talk(self._click_pool()), 2.2)

    def _toggle_clock(self):
        """시계 펼침/접힘 — 창 높이를 바꾸고(아래 고정) 좌표·그림자 재계산."""
        self.clock_open = not self.clock_open
        self.us["clock_open"] = self.clock_open
        self._save_settings()
        old_oy, old_H = self.oy, self.H
        old_x, old_y = self.root.winfo_x(), self.root.winfo_y()
        self.oy = self._timer_oy()
        self.H = self.ch_px + self.oy
        d = self.oy - old_oy
        self.canvas.config(height=self.H)
        self.root.geometry(f"{self.W}x{self.H}+{old_x}+{old_y - (self.H - old_H)}")
        self._pen_xy[1] += d                 # 좌표계가 d만큼 내려가므로 펜도 이동
        self._bake_oy()
        self._build_shadow_img()
        if self.shadow is not None and self.shadow_img is not None:
            self.shadow.set_image(self.shadow_img)

    def close(self):
        try:
            # 예약해 둔 다음 프레임을 먼저 거둔다. 안 그러면 창을 닫은 뒤에
            # 그 프레임이 없어진 창을 불러 'invalid command name' 이 뜬다.
            if self._tick_after is not None:
                try:
                    self.root.after_cancel(self._tick_after)
                except Exception:
                    pass
                self._tick_after = None
            if self.timer_on and self.ws_path is None:
                self._timer_save()
            if self._kb is not None:
                self._kb.stop()
            if self._ms is not None:
                self._ms.stop()
            if self.tray is not None:
                self.tray.close()
            if self.todo_panel is not None:
                self.todo_panel.destroy()
            if self.due_panel is not None:
                self.due_panel.destroy()
            # 살아있음 신호를 지운다. 안 지우면 에이전트가 최대 8초 동안
            # '아직 떠 있다'고 착각해서, 그 사이 아이콘을 눌러도 캐릭터가
            # 안 뜨고 클릭이 그냥 삼켜진다.
            if self.ws_path is not None:
                try:
                    base = os.path.dirname(self.ws_path)
                    os.remove(os.path.join(base, ".mascot_live"))
                    try:
                        os.remove(os.path.join(base, ".mascot_pid"))
                    except OSError:
                        pass
                except OSError:
                    pass
        finally:
            self.root.destroy()

    # ── 타이머 ───────────────────────────────────────────────────────────
    def _timer_load(self):
        # 자동 초기화 없음 — 우클릭 '타이머 초기화'로만 리셋 (확정 방침)
        try:
            with open(self.state_path, encoding="utf-8") as fp:
                st = json.load(fp)
            self.work_secs = float(st.get("seconds", 0))
            self.zero_at = float(st.get("zero_at", 0) or 0)
            self.goal_cheered = str(st.get("goal_cheered", "") or "")
            saved = st.get("stat")
            if isinstance(saved, dict):
                self.stat.update({k: saved.get(k, v) for k, v in self.stat.items()})
            r = st.get("rec")
            if isinstance(r, dict):      # 세션이 이어지면 축하 기록도 이어받는다
                self.rec["strokes"] = [int(v) for v in r.get("strokes", [])
                                       if isinstance(v, (int, float))]
                self.rec["focus"] = float(r.get("focus", 0) or 0)
        except Exception:
            pass

    def _timer_save(self):
        try:
            with open(self.state_path, "w", encoding="utf-8") as fp:
                json.dump({"seconds": round(self.work_secs),
                           "zero_at": round(self.zero_at),
                           "goal_cheered": self.goal_cheered,
                           "stat": self.stat, "rec": self.rec}, fp)
        except Exception:
            pass

    HIST_DAYS = 60               # 하루 기록을 며칠치 보관할지

    def _day_hour(self):
        """하루가 바뀌는 시각 (환경설정). 사람마다 생활 리듬이 달라서 연다."""
        try:
            return max(0, min(12, int(self.us.get("day_start", 6))))
        except Exception:
            return 6

    def _my_workday(self, ts=None):
        """이 캐릭터 기준의 작업일. 기록은 '시작한 시각'으로 날짜를 정한다.

        끝낸 시각으로 정하면 밤 10시~새벽 4시 작업이 다음 날로 밀려서,
        이틀치 작업이 하루에 뭉치고 앞날이 빈 날이 된다.
        """
        return _workday(ts, self._day_hour())

    def _session_day(self):
        """이번 작업의 날짜 — 처음 일한 시각 기준 (없으면 지금)."""
        first = self.stat.get("first") or 0
        return self._my_workday(first if first else None)
    GOAL_TALK = ("목표 달성! 오늘 대단했어.", "목표 채웠어! 잘했어.",
                 "오늘 목표 끝! 멋지다.")

    def _goal_tick(self, now):
        """목표 시간을 채우면 한 번 축하한다 (작업일마다 한 번)."""
        if not (self.cfg.get("goal_cheer") and self.can_cheer):
            return
        today = self._my_workday()        # 축하는 '지금'이 어느 작업일인지로
        if self.goal_cheered == today:
            return
        goal = max(float(self.us.get("goal_hours", 6)), 0.5) * 3600
        if self._shown_secs() < goal:
            return
        self.goal_cheered = today
        self._timer_save()
        self.hat_until = now + 12.0
        self.smile_until = now + 5.0
        # 목표를 채운 날은 만세 또는 박수 — 둘 중 하나가 번갈아 나오게 한다.
        # 새 동작이 꺼진 캐릭터에서는 만세가 무시되므로 그대로 박수가 된다.
        if random.random() < 0.5:
            self._gest_start("cheer", force=True)
        if self.gest != "cheer":
            self._gest_start("clap", force=True)
        pool = self.cfg.get("goal_talk") or self.GOAL_TALK
        self._say(random.choice(list(pool)), 6.0)
        self._safe("burst", self._burst, 40, 66)

    # ── 마감 목록 ────────────────────────────────────────────────────────
    DUE_NEAR, DUE_SOON = 1, 3        # 이 날짜 안이면 색이 바뀐다

    def _due_load(self):
        try:
            with open(os.path.join(self.state_dir, ".dues.json"),
                      encoding="utf-8") as fp:
                d = json.load(fp)
            items = d.get("items", []) if isinstance(d, dict) else []
            self.dues = [{"name": str(i.get("name", ""))[:60],
                          "date": str(i.get("date", ""))}
                         for i in items if str(i.get("date", "")).strip()][:20]
            if isinstance(d, dict):
                p_ = d.get("pos")
                if isinstance(p_, (list, tuple)) and len(p_) == 2:
                    self.due_pos = (int(p_[0]), int(p_[1]))
                self.due_flip = bool(d.get("flip"))
                self.due_zoom = TodoPanel._near_zoom(d.get("zoom", 100))
        except Exception:
            self.dues = []

    def _due_save(self):
        try:
            with open(os.path.join(self.state_dir, ".dues.json"), "w",
                      encoding="utf-8") as fp:
                json.dump({"items": self.dues, "pos": self.due_pos,
                           "flip": self.due_flip, "zoom": self.due_zoom},
                          fp, ensure_ascii=False)
        except Exception:
            pass

    @staticmethod
    def _days_to(datestr):
        """그 날짜까지 남은 날 수. 마감은 달력 날짜로 센다."""
        try:
            t = time.mktime(time.strptime(str(datestr), "%Y-%m-%d"))
        except Exception:
            return None
        today = time.mktime(time.strptime(time.strftime("%Y-%m-%d"), "%Y-%m-%d"))
        return int(round((t - today) / 86400))

    def _due_lines(self):
        """말풍선에 넣을 글과 색 — 가까운 마감부터 위로."""
        rows = []
        for d in self.dues:
            n = self._days_to(d.get("date"))
            if n is None:
                continue
            tag = "D-DAY" if n == 0 else (f"D-{n}" if n > 0 else f"D+{-n}")
            name = (d.get("name") or "").strip()
            rows.append((n, (name + "\n" + tag) if name else tag))
        rows.sort(key=lambda r: r[0])
        texts = [t for _, t in rows]
        tints = ["#d64a63" if n <= self.DUE_NEAR else
                 "#e08a3c" if n <= self.DUE_SOON else None for n, _ in rows]
        return texts, tints

    def _due_refresh(self):
        if self.due_panel is None:
            return
        texts, tints = self._due_lines()
        self.due_panel.render(texts, tints)
        self.due_panel.place(self.root.winfo_rootx(), self.root.winfo_rooty())
        self._due_shown = time.strftime("%Y-%m-%d")

    def _due_moved(self, x, y):
        self.due_pos = (int(x - self.root.winfo_rootx()),
                        int(y - self.root.winfo_rooty()))
        if self.due_panel is not None:
            self.due_panel.offset = self.due_pos
            self.due_panel._moved_by_user = True
        self._last_pos = None
        self._due_save()

    def _due_flipped(self, flip):
        self.due_flip = bool(flip)
        self._due_save()
        self._due_refresh()

    def _due_zoomed(self, pct):
        self.due_zoom = int(pct)
        self._due_save()
        self._last_pos = None
        self._due_refresh()

    def _due_remove(self, idx):
        """말풍선 우클릭 > 완료 — 그 마감을 목록에서 지운다."""
        order = sorted(range(len(self.dues)),
                       key=lambda i: (self._days_to(self.dues[i]["date"])
                                      if self._days_to(self.dues[i]["date"])
                                      is not None else 99999))
        if not (0 <= idx < len(order)):
            return
        self.dues.pop(order[idx])
        self._due_save()
        self._due_refresh()
        self._say("하나 끝났네!", 3.0)

    def _due_edit(self, idx):
        order = sorted(range(len(self.dues)),
                       key=lambda i: (self._days_to(self.dues[i]["date"])
                                      if self._days_to(self.dues[i]["date"])
                                      is not None else 99999))
        if 0 <= idx < len(order):
            self.add_due(edit=order[idx])

    def add_due(self, edit=None):
        """마감 입력 창 — 이름과 날짜. 엔터로 저장, Esc로 닫기."""
        if getattr(self, "_due_win", None) is not None                 and self._due_win.winfo_exists():
            self._due_win.destroy()
        cd, u = self.card, self._ui
        W, H = u(320), u(176)
        win = tk.Toplevel(self.root)
        self._due_win = win
        win.title("마감 수정" if edit is not None else "마감 추가")
        win.attributes("-topmost", True)
        win.resizable(False, False)
        win.configure(bg=cd["panel"])
        cv = tk.Canvas(win, width=W, height=H, bg=cd["panel"],
                       highlightthickness=0)
        cv.pack()

        def rr(x0, y0, x1, y1, r, **kw):
            pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1,
                   x1 - r, y1, x0 + r, y1, x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]
            return cv.create_polygon(pts, smooth=True, **kw)

        rr(u(14), u(12), W - u(14), u(44), u(12), fill=cd["soft"],
           outline=cd["border"], width=2)
        cv.create_text(W / 2, u(28), text="언제까지 끝낼까요?",
                       font=self._uf(10, True), fill=cd["text"])
        cur = self.dues[edit] if (edit is not None
                                  and edit < len(self.dues)) else {}
        nv = tk.StringVar(value=cur.get("name", ""))
        dv = tk.StringVar(value=cur.get("date", time.strftime("%Y-%m-%d")))
        ents = []
        for i, (lab, var) in enumerate((("이름", nv), ("날짜", dv))):
            ry = u(58) + i * u(38)
            cv.create_text(u(22), ry + u(13), anchor="w", text=lab,
                           font=self._uf(9), fill=cd["sub"])
            e = tk.Entry(win, textvariable=var, font=self._uf(10),
                         relief="flat", bg="#ffffff", fg=cd["text"],
                         highlightthickness=1, highlightbackground=cd["border"],
                         highlightcolor=cd["fill"])
            cv.create_window(u(58), ry, anchor="nw", window=e,
                             width=W - u(80), height=u(26))
            ents.append(e)
        cv.create_text(W / 2, u(150), text="날짜는 2026-08-15 처럼 · Esc로 닫기",
                       font=self._uf(8), fill=cd["sub"])

        def commit(_e=None):
            name = nv.get().strip()[:60]
            date = dv.get().strip()
            if self._days_to(date) is None:      # 날짜가 틀리면 그 칸으로
                ents[1].focus_set()
                ents[1].selection_range(0, "end")
                return
            item = {"name": name, "date": date}
            if edit is not None and edit < len(self.dues):
                self.dues[edit] = item
                self._due_save()
                self._due_refresh()
                win.destroy()
                return
            self.dues.append(item)
            del self.dues[20:]
            self._due_save()
            self._due_refresh()
            win.destroy()

        for e in ents:
            e.bind("<Return>", commit)
        win.bind("<Escape>", lambda _e: win.destroy())
        win.update_idletasks()
        sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
        px = min(max(self.root.winfo_rootx() - 40, 10), max(sw - W - 10, 10))
        py = min(max(self.root.winfo_rooty() - 20, 10), max(sh - H - 60, 10))
        win.geometry(f"+{int(px)}+{int(py)}")
        ents[0].focus_force()

    def _hist_load(self):
        """날짜별 하루 기록 {"2026-07-30": {...}}."""
        try:
            with open(os.path.join(self.state_dir, ".history.json"),
                      encoding="utf-8") as fp:
                d = json.load(fp)
            return d.get("days", {}) if isinstance(d, dict) else {}
        except Exception:
            return {}

    def _hist_add(self):
        """작업 종료 때 그날 기록에 더한다. 하루에 여러 번 끝내면 합산된다."""
        if not self.cfg.get("history"):
            return
        days = self._hist_load()
        key = self._session_day()
        cur = days.get(key) or {}
        s_ = self.stat
        days[key] = {
            "work": int(cur.get("work", 0)) + int(self._shown_secs()),
            "strokes": int(cur.get("strokes", 0)) + int(s_.get("strokes", 0)),
            "keys": int(cur.get("keys", 0)) + int(s_.get("keys", 0)),
            "best": max(int(cur.get("best", 0)), int(s_.get("best", 0))),
            "runs": int(cur.get("runs", 0)) + 1,
        }
        for k in sorted(days)[:-self.HIST_DAYS]:      # 오래된 것부터 버린다
            days.pop(k, None)
        try:
            with open(os.path.join(self.state_dir, ".history.json"), "w",
                      encoding="utf-8") as fp:
                json.dump({"days": days}, fp, ensure_ascii=False)
        except Exception:
            pass

    def _hist_summary(self):
        """브리핑에 붙일 요약 — 어제 대비 · 최근 7일 · 연속 일수."""
        days = self._hist_load()
        if not days:
            return None
        # 기준일은 '지금'이 아니라 이번 작업이 기록된 날이어야 한다.
        # 밤을 새워 경계를 넘으면 기록은 시작한 날에 들어가는데 여기서 지금
        # 날짜를 쓰면, 오늘 기록을 '어제'로 보여 주고 연속도 끊긴 것으로 센다.
        today = self._session_day()

        def shift(key, n):
            t = time.mktime(time.strptime(key, "%Y-%m-%d")) + n * 86400
            return time.strftime("%Y-%m-%d", time.localtime(t))

        yday = days.get(shift(today, -1), {}).get("work", 0)
        week = sum(int(days.get(shift(today, -i), {}).get("work", 0))
                   for i in range(7))
        streak, i = 0, 0
        while int(days.get(shift(today, -i), {}).get("work", 0)) >= 600:
            streak += 1
            i += 1
        return {"yday": int(yday), "week": int(week), "streak": streak}

    # ── 만든 사람에게 보내는 한마디 ──────────────────────────────────────
    FB_MAX = 800                 # 한 번에 보낼 수 있는 글자 수
    FB_COOL = 30                 # 연달아 보내는 것 방지 (초)

    FB_KEY = b"ena-mascot-feedback"

    @staticmethod
    def _unmask(blob):
        """가려 놓은 주소를 푼다.

        보안 수단이 아니라, 배포 레포가 공개라서 자동 스캐너가 주소를 찾아
        웹훅을 폐기해 버리는 것을 막으려는 것이다. 프로그램을 뜯으면 누구나
        볼 수 있으니, 문제가 생기면 웹훅을 새로 만들어 다시 배포하면 된다.
        """
        try:
            raw = _b64.b64decode(str(blob).encode())
            k = Mascot.FB_KEY
            return bytes(c ^ k[i % len(k)] for i, c in enumerate(raw)).decode()
        except Exception:
            return ""

    def _fb_url(self):
        url = str(self.cfg.get("feedback_url") or "").strip()
        return url or self._unmask(self.cfg.get("feedback_url_enc") or "")

    def _fb_path(self):
        return os.path.join(self.state_dir, ".feedback_queue.json")

    def _fb_send(self, text):
        """건의를 보낸다. 실패하면 파일에 담아 두었다가 다음에 다시 보낸다.

        보내는 것은 사용자가 적은 글과 캐릭터 이름·버전뿐이다. 컴퓨터 정보나
        작업 기록 같은 것은 보내지 않는다.
        """
        text = str(text).strip()[:self.FB_MAX]
        if not text:
            return False, "내용을 적어 주세요."
        now = time.time()
        if now - getattr(self, "_fb_last", 0) < self.FB_COOL:
            return False, "잠시 뒤에 다시 보내 주세요."
        self._fb_last = now
        self._fb_queue_add(text)
        threading.Thread(target=self._fb_flush, daemon=True).start()
        return True, "보냈어요. 고마워요!"

    def _fb_queue_add(self, text):
        try:
            items = self._fb_queue_load()
            items.append({"text": text, "ts": time.time(),
                          "char": self.cfg.get("name", self.char),
                          "ver": self._my_version()})
            with open(self._fb_path(), "w", encoding="utf-8") as fp:
                json.dump(items[-20:], fp, ensure_ascii=False)
        except Exception:
            pass

    def _my_version(self):
        """배포 매니페스트에 적힌 버전 (없으면 빈 문자열)."""
        try:
            with open(os.path.join(os.path.dirname(self.dir), "version.json"),
                      encoding="utf-8") as fp:
                return str(json.load(fp).get("version") or "")
        except Exception:
            return ""

    def _fb_queue_load(self):
        try:
            with open(self._fb_path(), encoding="utf-8") as fp:
                v = json.load(fp)
            return v if isinstance(v, list) else []
        except Exception:
            return []

    def _fb_flush(self):
        """쌓인 건의를 보낸다 (백그라운드). 못 보내면 그대로 남겨 둔다."""
        import urllib.request
        url = self._fb_url()
        items = self._fb_queue_load()
        if not (url and items):
            return
        left = []
        for it in items:
            when = time.strftime("%Y-%m-%d %H:%M",
                                 time.localtime(it.get("ts", time.time())))
            head = (f"**{it.get('char', '')}** · {when}"
                    f" · v{it.get('ver', '')}")
            body = head + "\n" + str(it.get("text", ""))
            try:
                req = urllib.request.Request(
                    url, data=json.dumps({"content": body[:1900]}).encode(),
                    headers={"Content-Type": "application/json",
                             "User-Agent": "mascot-feedback"}, method="POST")
                with urllib.request.urlopen(req, timeout=15) as r:
                    if r.status >= 300:
                        left.append(it)
            except Exception:
                left.append(it)
        try:
            if left:
                with open(self._fb_path(), "w", encoding="utf-8") as fp:
                    json.dump(left, fp, ensure_ascii=False)
            elif os.path.exists(self._fb_path()):
                os.remove(self._fb_path())
        except Exception:
            pass

    def _tray_ico_path(self):
        """트레이에 쓸 머리 아이콘 파일을 만들어 두고 그 경로를 준다.

        선물 exe에는 .ico가 안 들어 있을 수 있어서, 파츠로 그때그때 만든다.
        만들어 둔 것이 파츠보다 새것이면 다시 만들지 않는다.
        """
        out = os.path.join(self.state_dir, ".tray.ico")
        base = "head" if self.has_part("head") else "body_open"
        src = os.path.join(self.parts_dir, f"{base}.png")
        try:
            if (os.path.exists(out) and os.path.exists(src)
                    and os.path.getmtime(out) >= os.path.getmtime(src)):
                return out
        except OSError:
            pass
        try:
            cw, ch = self.layout["canvas"]
            sheet = Image.new("RGBA", (cw, ch), (0, 0, 0, 0))

            def put(name):
                pth = os.path.join(self.parts_dir, f"{name}.png")
                if os.path.exists(pth) and name in self.layout:
                    sheet.alpha_composite(Image.open(pth).convert("RGBA"),
                                          tuple(self.layout[name]["pos"]))
            put(base)
            put("pupils")
            for n in (self.layout.get("overlays") or []):
                if n in ("lashes", "hair"):
                    put(n)
            hb = Image.open(src).convert("RGBA").split()[3].getbbox()
            hx, hy = self.layout[base]["pos"]
            crop = sheet.crop((hx + hb[0], hy + hb[1], hx + hb[2], hy + hb[3]))
            bb = crop.split()[3].getbbox()
            if bb:
                crop = crop.crop(bb)
            side = int(max(crop.size) * 1.06)
            sq = Image.new("RGBA", (side, side), (0, 0, 0, 0))
            sq.alpha_composite(crop, ((side - crop.width) // 2,
                                      (side - crop.height) // 2))
            sq.resize((256, 256), Image.LANCZOS).save(
                out, sizes=[(16, 16), (20, 20), (24, 24), (32, 32), (48, 48)])
            return out
        except Exception:
            self._log_error("tray_ico")
            return ""

    def _tray_setup(self):
        """트레이 아이콘 올리기 — 왼쪽 클릭은 부르기, 오른쪽은 메뉴."""
        if not (IS_WIN and self.cfg.get("tray", True)):
            return
        ico = self._tray_ico_path()
        if not ico:
            return
        name = str(self.cfg.get("name", self.char))
        self.tray = TrayIcon(ico, f"{name} 타이머",
                             lambda: self._tray_q.append("call"),
                             lambda: self._tray_q.append("menu"))

    def _tray_tick(self):
        """트레이에서 누른 것을 그리기 루프에서 처리한다 (스레드 분리)."""
        while self._tray_q:
            what = self._tray_q.pop(0)
            if what == "menu":
                self._tray_menu()
            else:
                self._tray_call()

    def _tray_menu(self):
        """트레이 우클릭 메뉴 — 바깥을 누르면 그냥 닫히게.

        메뉴를 띄울 때 우리 창이 맨 앞(포그라운드)이 아니면, 윈도우가 바깥
        클릭을 메뉴에 전달하지 않아 메뉴가 계속 떠 있는다. 트레이 아이콘을
        누른 시점의 맨 앞 창은 사용자가 쓰던 프로그램이라 늘 이 상태가 된다.
        메뉴를 띄우기 직전에 창을 맨 앞으로 올려 두면 정상적으로 닫힌다.
        (트레이 프로그램이 쓰는 정석 방법 — 메뉴가 닫힌 뒤 빈 메시지를 보내
        윈도우가 메뉴 상태를 정리하게 한다.)
        """
        x, y = cursor_pos()
        hwnd = getattr(self, "_main_hwnd", 0)
        u = ctypes.windll.user32 if IS_WIN else None
        if u is not None and hwnd:
            try:
                u.SetForegroundWindow(hwnd)
            except Exception:
                pass
        try:
            self._menu.tk_popup(int(x), int(y))
        finally:
            self._menu.grab_release()
            if u is not None and hwnd:
                try:
                    u.PostMessageW(hwnd, 0x0000, 0, 0)   # WM_NULL
                except Exception:
                    pass

    def _tray_call(self):
        """캐릭터를 불러온다 — 화면 밖이면 보이는 자리로 끌어온다."""
        self.root.deiconify()
        self.root.lift()
        self.root.attributes("-topmost", True)
        if not self.us.get("topmost", True):
            self.root.after(1200, lambda: self.root.attributes("-topmost", False))
        x, y = self.root.winfo_x(), self.root.winfo_y()
        ml, mt, mr, mb = monitor_at(*cursor_pos())
        if not (ml - 20 <= x <= mr - 40 and mt - 20 <= y <= mb - 60):
            self.root.geometry(f"+{mr - self.W - 60}+{mb - self.H - 90}")
            self._safe("win_pos", self._save_win_pos)
        self._say("여기 있어요!", 2.2)

    def _load_win_pos(self, sw, sh):
        """지난번에 두었던 자리. 없거나 화면 밖이면 기본 자리(오른쪽 아래)로.

        모니터 구성이 바뀌면 저장된 자리가 화면 밖일 수 있으므로, 창이 화면에
        조금이라도 걸치는지 확인하고 아니면 기본 자리로 되돌린다.
        """
        base = (sw - self.W - 50, sh - self.H - 70)
        if not self.cfg.get("remember_pos"):
            return base
        try:
            with open(self.ui_prefs_path, encoding="utf-8") as fp:
                d = json.load(fp)
            x, y = int(d["win_x"]), int(d["win_y"])
        except Exception:
            return base
        vx = self.root.winfo_vrootx() if hasattr(self.root, "winfo_vrootx") else 0
        vy = self.root.winfo_vrooty() if hasattr(self.root, "winfo_vrooty") else 0
        vw = max(self.root.winfo_vrootwidth(), sw)
        vh = max(self.root.winfo_vrootheight(), sh)
        if (x + self.W < vx + 40 or x > vx + vw - 40
                or y + self.H < vy + 40 or y > vy + vh - 40):
            return base                      # 그 자리에 이제 화면이 없다
        return (x, y)

    def _save_win_pos(self):
        """지금 자리를 기억해 둔다 — 끌어 놓을 때마다 바로 (강제 종료 대비)."""
        if not self.cfg.get("remember_pos"):
            return
        try:
            self.root.update_idletasks()      # 방금 옮긴 자리가 반영된 뒤 읽는다
            d = {}
            if os.path.exists(self.ui_prefs_path):
                with open(self.ui_prefs_path, encoding="utf-8") as fp:
                    d = json.load(fp) or {}
            d["win_x"] = int(self.root.winfo_x())
            d["win_y"] = int(self.root.winfo_y())
            with open(self.ui_prefs_path, "w", encoding="utf-8") as fp:
                json.dump(d, fp)
        except Exception:
            pass

    def _shown_secs(self):
        """카드에 보여 줄 시간. 작업 종료를 누른 뒤로 다시 센 만큼만.

        누적 자체(work_secs)는 그대로 두고 기준점만 옮긴다. 기존 타이머가
        보내 주는 값을 덮어쓰면 다음 갱신에 바로 되돌아오기 때문이다.
        """
        if self.work_secs < self.zero_at:     # 작업일이 넘어가 누적이 줄었다
            self.zero_at = 0.0
        return max(0.0, self.work_secs - self.zero_at)

    def _reset_records(self):
        """새 세션 — 기록 갱신 축하를 처음부터 다시 센다."""
        self.rec = {"strokes": [], "focus": 0.0}
        self._rec_prev_run = 0.0
        self._rec_armed = True

    def _timer_reset(self):
        self.work_secs = 0.0
        self.zero_at = 0.0
        self._reset_records()
        self._timer_save()

    @staticmethod
    def _app_key(s):
        """앱 이름 비교용 정규화 — 확장자·공백·기호를 지우고 소문자로.

        윈도우는 실행파일 이름('clipstudiopaint.exe'), 맥은 앱 표시 이름
        ('CLIP STUDIO PAINT')이라 그대로 비교하면 같은 프로그램도 안 맞는다.
        둘 다 'clipstudiopaint'로 만들어 비교한다.
        """
        s = str(s).lower()
        for ext in (".exe", ".app"):
            if s.endswith(ext):
                s = s[:-len(ext)]
        return "".join(ch for ch in s if ch.isalnum())

    def _fg_is_self(self):
        """앞 창이 이 프로그램 자신의 창인가 (캐릭터·설정·말풍선 모두 포함)."""
        if not IS_WIN:
            return False
        try:
            u = ctypes.windll.user32
            pid = ctypes.c_ulong()
            u.GetWindowThreadProcessId(u.GetForegroundWindow(),
                                       ctypes.byref(pid))
            return pid.value == os.getpid()
        except Exception:
            return False

    def _fg_is_work(self, now):
        """앞 창이 작업 프로그램인지 (1초 캐시).

        캐릭터를 누르면 잠깐 이 창이 앞으로 온다. 그걸 '작업 아님'으로 세면
        스트레칭 알림을 끄려고 누른 것만으로 최장 집중 기록이 끊긴다.
        자기 창일 때는 직전 판정을 그대로 유지한다.
        """
        if now - self._fg_checked > 1.0 and not self._fg_is_self():
            self._fg_checked = now
            fg = self._app_key(foreground_process())
            apps = [self._app_key(a) for a in
                    str(self.us["work_apps"]).split(",") if a.strip()]
            self._fg_work = bool(fg) and any(a and (a == fg or a in fg or fg in a)
                                             for a in apps)
        return self._fg_work

    def _timer_tick(self, now, idle):
        """상태 반환: work(측정)/other(작업앱 아님)/idle(휴식)/off(연동 끊김)."""
        if self.ws_path is not None:
            # 워크스페이스 워크타이머 연동: 에이전트의 라이브 파일을 읽어 표시만 한다
            if now - self._ws_read > 1.0:
                self._ws_read = now
                try:
                    with open(self.ws_path, encoding="utf-8") as fp:
                        self._ws_data = json.load(fp)
                except Exception:
                    self._ws_data = None
            d = self._ws_data
            # 기존 타이머가 꺼졌거나(프로세스 종료), 떠 있어도 '작업 종료' 상태라
            # 시간을 세지 않는 경우 모두 캐릭터가 이어서 잰다.
            # (세션이 꺼진 걸 몰라서 아무도 안 세는 사이 작업 시간이 통째로
            #  사라지던 문제 — 캐릭터 화면에는 옛 누적값이 그대로 보여 더 헷갈렸다)
            ws_down    = (not d) or (now - float(d.get("ts", 0)) > 8)
            ws_no_sess = bool(d) and not d.get("session_on", True)
            if ws_down or ws_no_sess:
                if not self._ws_lost:
                    self._ws_lost = True
                    self._t_last = now
                    self._solo_from = self.work_secs   # 여기서부터 혼자 잰 시간
                return self._own_tick(now, idle)
            if self._ws_lost:         # 기존 타이머가 돌아왔다 — 다시 따라간다
                self._ws_lost = False
            self.work_secs = float(d.get("total", 0))
            if d.get("active"):
                state = "work"
            elif d.get("idle") or idle >= self.idle_thr:
                state = "idle"
            else:
                state = "other"
            # 연동 모드에서도 집중 구간을 쌓아야 '최장 집중 갱신'이 뜬다
            dt = min(max(now - self._t_last, 0.0), 2.0)
            self._t_last = now
            st = self.stat
            st[state] = st.get(state, 0.0) + dt
            if state == "work":
                st["_run"] = st.get("_run", 0.0) + dt
                st["best"] = max(st.get("best", 0.0), st["_run"])
                if not st.get("first"):
                    st["first"] = now
                st["last"] = now
            else:
                st["_run"] = 0.0
            return state

        return self._own_tick(now, idle)

    def _own_tick(self, now, idle):
        """캐릭터가 직접 재는 경로 (연동 없는 캐릭터 + 연동이 끊겼을 때)."""
        dt = min(max(now - self._t_last, 0.0), 2.0)
        self._t_last = now
        if idle >= self.idle_thr:
            state = "idle"
        elif self.us["work_apps_only"] and not self._fg_is_work(now):
            state = "other"
        else:
            state = "work"
            self.work_secs += dt
        # 하루 브리핑용 집계 (작업/딴짓/휴식 시간, 최장 집중 구간, 시작·마지막)
        s = self.stat
        s[state] = s.get(state, 0.0) + dt
        if state == "work":
            s["_run"] = s.get("_run", 0.0) + dt
            s["best"] = max(s.get("best", 0.0), s["_run"])
            if not s.get("first"):
                s["first"] = now
            s["last"] = now
        else:
            s["_run"] = 0.0
        if now - self._t_save > 30:
            self._t_save = now
            self._timer_save()
        return state

    def _text_w(self, text):
        """상태 텍스트 폭(px) — 캔버스로 측정·캐시 (tkinter.font 의존 제거)."""
        w = self._tw_cache.get(text)
        if w is None:
            t = self.canvas.create_text(-2000, -2000, text=text, anchor="nw",
                                        font=("Malgun Gothic", 8))
            bb = self.canvas.bbox(t)
            w = (bb[2] - bb[0]) if bb else len(text) * 11
            self.canvas.delete(t)
            self._tw_cache[text] = w
        return w

    def _rrect(self, x0, y0, x1, y1, r, **kw):
        pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1,
               x1 - r, y1, x0 + r, y1, x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]
        return self.canvas.create_polygon(pts, smooth=True, **kw)

    @staticmethod
    def _ear_pts(cx, cy, droop, k=1.0):
        """카드 위 토끼 귀 윤곽 (베지에 척추 + 폭). droop=1이면 옆으로 접힌다."""
        p0 = (cx, cy)
        if droop:
            p1, p2 = (cx + 1, cy - 28), (cx + 24, cy - 16)
        else:
            p1, p2 = (cx - 4, cy - 26), (cx + 1, cy - 33)
        left, right, cap, N = [], [], [], 8
        for i in range(N + 1):
            t = i / N
            u = 1 - t
            x = u * u * p0[0] + 2 * u * t * p1[0] + t * t * p2[0]
            y = u * u * p0[1] + 2 * u * t * p1[1] + t * t * p2[1]
            dx = 2 * u * (p1[0] - p0[0]) + 2 * t * (p2[0] - p1[0])
            dy = 2 * u * (p1[1] - p0[1]) + 2 * t * (p2[1] - p1[1])
            n = math.hypot(dx, dy) or 1.0
            tx, ty = dx / n, dy / n
            nx, ny = -ty, tx
            w = (1.8 + 4.6 * math.sin(math.pi * (0.18 + 0.74 * t))) * k
            left.append((x + nx * w, y + ny * w))
            right.append((x - nx * w, y - ny * w))
            if i == N:                       # 귀 끝은 반원으로 둥글게
                for j in range(1, 5):
                    th = math.pi * j / 5
                    ct, st = math.cos(th), math.sin(th)
                    cap.append((x + (ct * nx + st * tx) * w,
                                y + (ct * ny + st * ty) * w))
        return [v for p in left + cap + right[::-1] for v in p]

    def _draw_deco(self, x0, y0, x1, y1):
        """카드 위 장식(귀 등) — 캐릭터 컨셉별."""
        c = self.canvas
        deco = self.card["deco"]
        if deco == "panda":
            for ex in (x0 + 26, x1 - 26):
                c.create_oval(ex - 12, y0 - 17, ex + 12, y0 + 7,
                              fill="#2b2b2b", outline="")
                c.create_oval(ex - 6, y0 - 11, ex + 6, y0 + 1,
                              fill="#4a4a4a", outline="")
        elif deco == "cat":
            for sign, ex in ((-1, x0 + 26), (1, x1 - 26)):
                c.create_polygon(ex - 13 * sign, y0 + 5, ex + 3 * sign, y0 - 17,
                                 ex + 13 * sign, y0 + 3,
                                 fill="#f5bdd2", outline="#d687ab", width=2)
                c.create_polygon(ex - 6 * sign, y0 + 2, ex + 3 * sign, y0 - 10,
                                 ex + 8 * sign, y0 + 1,
                                 fill="#eba0c0", outline="")
        elif deco == "dog":
            # 접힌 검은 강아지 귀 — 카드 위 모서리에서 바깥으로 늘어짐
            for sign, ex in ((-1, x0 + 18), (1, x1 - 18)):
                c.create_oval(ex - 15, y0 - 15, ex + 9, y0 + 28,
                              fill="#2b2b2b", outline="")
                c.create_oval(ex - 9, y0 - 7, ex + 3, y0 + 14,
                              fill="#4a4a4a", outline="")
        elif deco == "rabbit":
            base = self.card.get("bg", "#ffffff")
            inner = self.card.get("track", "#c9d3e6")
            for sign, ex in ((-1, x0 + 26), (1, x1 - 34)):
                droop = 1 if sign > 0 else 0        # 오른쪽 귀는 접혀 내려감
                c.create_polygon(self._ear_pts(ex, y0 + 10, droop),
                                 smooth=True, fill=base,
                                 outline=self.card["border"], width=2)
                c.create_polygon(self._ear_pts(ex, y0 + 8, droop, 0.42),
                                 smooth=True, fill=inner, outline="")
        elif deco == "scarf":
            navy, silver = "#2f3f66", "#dfe5f0"
            self._rrect(x0 + 14, y0 - 15, x1 - 14, y0 + 7, 9, fill=navy, outline="")
            span = (x1 - x0 - 76) / 3
            for i in range(4):
                sx = x0 + 44 + i * span
                c.create_line(sx, y0 - 13, sx - 7, y0 + 5, fill=silver, width=3)
        elif deco == "rose":
            for ex in (x0 + 26, x1 - 26):
                c.create_oval(ex - 12, y0 - 17, ex + 12, y0 + 7,
                              fill="#f5bdd2", outline="#d687ab", width=2)
                c.create_arc(ex - 8, y0 - 13, ex + 8, y0 + 3, start=300,
                             extent=270, style="arc", outline="#d687ab", width=2)
        elif deco == "ribbon":
            # 사가: 카드 위 한가운데 작은 분홍 리본
            mx = (x0 + x1) / 2
            fill, line = "#f9b6d2", "#e07aa8"
            for sign in (-1, 1):                    # 좌우 고리
                c.create_polygon(mx, y0 - 1, mx + 17 * sign, y0 - 14,
                                 mx + 19 * sign, y0 + 1, mx + 15 * sign, y0 + 6,
                                 smooth=True, fill=fill, outline=line, width=2)
            for sign in (-1, 1):                    # 아래로 늘어진 끈
                c.create_line(mx + 2 * sign, y0 + 3, mx + 7 * sign, y0 + 13,
                              fill=line, width=3)
            c.create_oval(mx - 5, y0 - 6, mx + 5, y0 + 4,
                          fill="#ffd9e8", outline=line, width=2)   # 가운데 매듭
        elif deco == "sprout":
            # 기뽀: 카드 위 한가운데 작은 새싹
            mx = (x0 + x1) / 2
            leaf, stem = "#8fc34a", "#5c8a2c"
            c.create_line(mx, y0 + 6, mx, y0 - 12, fill=stem, width=3)
            for sign in (-1, 1):                    # 좌우 잎
                c.create_polygon(mx, y0 - 9 - 2 * (sign > 0),
                                 mx + 8 * sign, y0 - 18,
                                 mx + 15 * sign, y0 - 10,
                                 mx + 6 * sign, y0 - 4,
                                 smooth=True, fill=leaf, outline=stem, width=2)

    def _status_of(self, state, sleeping):
        if self.stretch_pending and self.stretch_shown >= self.TAP_CARD_AT:
            return DOT_OTHER, "스트레칭!"
        if state == "off":
            return DOT_OFF, "타이머 꺼짐"
        if self._ws_lost and state == "work":
            return DOT_ON, "혼자 측정 중"
        if sleeping:
            return DOT_OFF, "자는 중"
        if state == "work":
            return DOT_ON, "작업중"
        if state == "other":
            return DOT_OTHER, "딴짓 중"
        return DOT_OFF, "쉬는 중"

    def _draw_clock(self, cx, cy, R, now):
        """아날로그 시계 + 작업한 시간을 방사형 선으로(기존 '작업 흔적' 방식).

        작업한 분마다 중심→가장자리 방향으로 선 하나(오전=연한색/오후=진한색).
        연속 작업이면 부채꼴처럼 촘촘히 채워지고, 안 한 시간대는 비어 있다.
        """
        c = self.canvas
        cd = self.card
        am_col = cd.get("arc_am", "#f4c9dd")     # 오전 = 연한 분홍
        pm_col = cd.get("arc_pm", "#e493bd")     # 오후 = 진한 분홍
        # 바탕
        c.create_oval(cx - R, cy - R, cx + R, cy + R,
                      fill=cd["bg"], outline=cd["border"], width=2)
        # 작업한 분 = 방사형 선 (12시간 다이얼 위치)
        Rf = R - 3
        seen = set()
        for m in ((self._ws_data or {}).get("act") or []):
            lt = time.localtime(m * 60)
            pos = (lt.tm_hour % 12) * 60 + lt.tm_min
            key = (pos, lt.tm_hour < 12)
            if key in seen:
                continue
            seen.add(key)
            a = math.radians(pos / 720 * 360 - 90)
            col = am_col if lt.tm_hour < 12 else pm_col
            c.create_line(cx, cy, cx + Rf * math.cos(a), cy + Rf * math.sin(a),
                          fill=col, width=1)
        # 시각 눈금
        for i in range(12):
            a = math.radians(i * 30 - 90)
            big = i % 3 == 0
            r2 = R - (8 if big else 5)
            c.create_line(cx + (R - 3) * math.cos(a), cy + (R - 3) * math.sin(a),
                          cx + r2 * math.cos(a), cy + r2 * math.sin(a),
                          fill=cd["sub"], width=2 if big else 1)
        lt = time.localtime(now)
        hh = lt.tm_hour % 12 + lt.tm_min / 60
        mm = lt.tm_min + lt.tm_sec / 60

        def hand(frac, length, width, color):
            a = math.radians(frac * 360 - 90)
            c.create_line(cx, cy, cx + length * math.cos(a), cy + length * math.sin(a),
                          width=width, fill=color, capstyle="round")

        hand(hh / 12, R * 0.46, 3, cd["text"])
        hand(mm / 60, R * 0.66, 2, cd["text"])
        hand(lt.tm_sec / 60, R * 0.76, 1, cd["fill"])
        c.create_oval(cx - 2.5, cy - 2.5, cx + 2.5, cy + 2.5, fill=cd["fill"], outline="")

    # ── 귀여운 이벤트: 말풍선 · 혼잣말 · 클릭 반응 · 반려동물 · 축하 ──────
    PET_RISE, PET_HOLD, PET_FALL = 0.5, 6.0, 0.5
    TALK = [
        "히히", "바보!", "배고파요", "조금만 더 힘내자!", "뭐 좀 먹고 할까...",
        "야옹", "싫어 그 가느다란 꼬리", "사탄 참 좋다", "가즈아", "야르",
        "졸려", "심심해", "오늘도 화이팅!", "집중! 집중!", "손이 멈췄다?",
        "그림 그리자!", "저장했지?", "Ctrl+S!", "커피 한 잔?", "조금만 더!",
        "쉬엄쉬엄 하자.", "손목 괜찮아?", "한 장만 더!", "끝내고 놀자!",
        "영혼을 바쳐라.", "몰?루", "오늘도 평화롭다.", "좋은 하루!",
        "기분 최고!", "운세 좋음!", "행운 냥!", "행복 충전!", "산책은 싫어.",
        "창밖이 궁금해.", "햇빛이다!", "꾸벅...", "후암~", "멍...", "어라?",
        "오?", "흠...", "비밀이야.", "쉿!", "냥냥펀치!", "히힛!",
        "간식은 언제?",
    ]
    CLICK_TALK = TALK

    def _say(self, text, secs=4.0):
        self.bubble = (text, time.time() + secs)

    def _talk_pool(self, state):
        return self.cfg.get("talk") or self.TALK

    def _pick_talk(self, pool):
        """최근에 한 말은 빼고 고른다 — 같은 말이 금방 또 나오면 김이 샌다.

        목록의 3분의 1 정도를 기억해 두고 그 밖에서 뽑는다. 목록이 짧으면
        기억하는 개수도 같이 줄어 항상 뽑을 게 남는다.
        """
        keep = max(1, min(len(pool) - 1, len(pool) // 3))
        recent = getattr(self, "_recent_talk", [])
        cand = [t for t in pool if t not in recent] or list(pool)
        pick = random.choice(cand)
        self._recent_talk = (recent + [pick])[-keep:]
        return pick

    def _click_pool(self):
        return self.cfg.get("click_talk") or self._talk_pool(None)

    def _fun_tick(self, now, state, sleeping):
        """혼잣말·반려동물 스케줄과 폭죽 물리 (매 프레임)."""
        # 말풍선 사라짐은 fun과 무관하게 항상 처리한다. 예전에는 fun이 꺼진
        # 캐릭터에서 한 번 뜬 말풍선이 영영 남았다.
        if self.bubble and now > self.bubble[1]:
            self.bubble = None
        if self.particles:
            self._step_particles()
        if self.notes:
            self._step_notes()
        if not self.fun and not self.can_cheer:
            return
        if not self.fun:
            self._rec_tick(now, state)
            return
        if self._update_msg and self.bubble is None and not sleeping:
            self._say(self._update_msg, 12.0)     # 업데이트 알림 (시작 후 한 번)
            self._update_msg = None
            self.next_talk = now + 120
            if self._update_notes:                # 무엇이 바뀌었는지 팝업으로
                self._safe("update_popup", self._show_update_popup)
        self._rec_tick(now, state)
        if (self.bubble is None and now >= self.next_talk
                and not sleeping and now > self.celebrate_until):
            line = self._pick_talk(self._talk_pool(state))
            self._say(line)
            self.next_talk = now + random.uniform(700, 1700)
            if random.random() < 0.4:         # 혼잣말하며 고개를 까딱
                self._gest_start(self._talk_gesture(line))
        # 반려동물 등장/퇴장
        total = self.PET_RISE + self.PET_HOLD + self.PET_FALL
        if self.pet_t0 == 0.0 and now >= self.next_pet and not sleeping:
            self.pet_cast = self._pick_pets()
            self.pet_t0 = now if self.pet_cast else 0.0
            if not self.pet_cast:
                self.next_pet = now + 999999
        elif self.pet_t0 and now - self.pet_t0 > total + 0.4:
            self.pet_t0 = 0.0
            self.next_pet = now + random.uniform(240, 600)

    def _step_particles(self):
        """폭죽 조각 (중력 + 수명)."""
        alive = []
        for p in self.particles:
            p[0] += p[2]
            p[1] += p[3]
            p[3] += 0.35
            p[5] -= 1
            if p[5] > 0 and p[1] < self.H + 30:
                alive.append(p)
        self.particles = alive

    STROKE_MARKS = (300, 1000, 3000, 10000)   # 그린 획수 축하 지점
    FOCUS_MIN = 20 * 60                       # 최장 집중은 20분부터 인정
    FOCUS_STEP = 60                           # 최소 이만큼은 넘겨야 '갱신'

    def _rec_tick(self, now, state):
        """기록 갱신 축하 — 그린 획수 돌파 · 이번 세션 최장 집중 갱신."""
        if not self.can_cheer or self.bubble is not None                 or now < self.celebrate_until:
            return
        if now < self._rec_next or state != "work":
            return                            # 작업 중일 때만, 그리고 쿨다운 뒤
        run = float(self.stat.get("_run", 0.0))
        if run < self._rec_prev_run:          # 집중이 끊겼다 → 다음 구간 준비
            self._rec_armed = True
        self._rec_prev_run = run

        strokes = int(self.stat.get("strokes", 0))
        for mark in self.STROKE_MARKS:
            if strokes >= mark and mark not in self.rec["strokes"]:
                self.rec["strokes"].append(mark)
                self._cheer(f"{mark:,}획 돌파!")
                return
        if (self._rec_armed and run >= self.FOCUS_MIN
                and run > self.rec["focus"] + self.FOCUS_STEP):
            self.rec["focus"] = run
            self._rec_armed = False           # 이 구간에서는 한 번만
            self._cheer(f"최장 집중 갱신! {int(run // 60)}분째")

    def _cheer(self, text):
        """작업 종료보다 약한 축하 — 말풍선 + 폭죽 조금 (팝업 없음)."""
        now = time.time()
        self._rec_next = now + 90             # 연달아 뜨지 않게
        for _ in range(2):                    # 기록 갱신은 반짝임
            self._safe("fx", self._spawn_note, now, "spark")
        self._say(text, 4.5)
        self._gest_start("clap", force=True)
        if self.has.get("smile"):
            self.smile_until = now + 3.0
        cols = ["#ff9ec4", "#ffd479", "#9ad7ff", "#b8e986", "#c9a7ff"]
        for _ in range(14):
            ang = random.uniform(-2.6, -0.55)
            spd = random.uniform(3.0, 6.5)
            self.particles.append([self.card_cx + random.uniform(-45, 45),
                                   self.oy + 46,
                                   math.cos(ang) * spd, math.sin(ang) * spd,
                                   random.choice(cols), random.randint(35, 60)])
        self._timer_save()

    def _pick_pets(self):
        """이번에 나올 반려동물 배역 — 2마리면 한 마리씩 또는 둘 다."""
        names = [n for n in ("pet1", "pet2") if self.has.get(n)]
        if len(names) < 2:
            return [(n, 0.0) for n in names]
        if self.cfg.get("pet_variants"):      # 같은 동물의 다른 포즈 — 하나만
            return [(random.choice(names), 0.0)]
        pick = random.choice([[names[0]], [names[1]], names])
        return [(n, i * 0.35) for i, n in enumerate(pick)]

    def _pet_img(self, name, dy):
        """책상 윗선 아래는 잘라낸 반려동물 이미지 (내려간 만큼 가려짐)."""
        key = (name, int(dy))
        hit = self._pet_cache.get(key)
        if hit is None:
            if len(self._pet_cache) > 120:
                self._pet_cache.clear()
            pil = self._pil_cache[name]
            x0, y0 = self._pet_xy[name]
            y0 = y0 + dy
            region = self._pet_mask.crop((x0, y0, x0 + pil.width, y0 + pil.height))
            blank = Image.new("RGBA", pil.size, (0, 0, 0, 0))
            cut = Image.composite(pil, blank, region)
            if name not in self._soft_parts:
                cut = self._hard(cut)
            hit = ImageTk.PhotoImage(cut)
            self._pet_cache[key] = hit
        return hit

    PET_BLUR = 16                    # 반려동물 그림자 블러 여백

    def _pet_shadow_pil(self, name, dy):
        """반려동물 그림자(책상선까지 잘린 실루엣을 흐린 것) — dy별 캐시."""
        key = (name, int(dy))
        hit = self._pet_sh_cache.get(key)
        if hit is None:
            from PIL import ImageFilter
            if len(self._pet_sh_cache) > 40:
                self._pet_sh_cache.clear()
            pil = self._pil_cache[name]
            x0, y0 = self._pet_xy[name]
            region = self._pet_mask.crop((x0, y0 + dy, x0 + pil.width,
                                          y0 + dy + pil.height))
            blank = Image.new("RGBA", pil.size, (0, 0, 0, 0))
            cut = Image.composite(pil, blank, region)
            b = self.PET_BLUR
            pad = Image.new("L", (pil.width + 2 * b, pil.height + 2 * b), 0)
            pad.paste(cut.getchannel("A"), (b, b))
            a = pad.filter(ImageFilter.GaussianBlur(7)).point(lambda v: int(v * 0.30))
            black = Image.new("RGB", pad.size, (0, 0, 0))
            hit = Image.merge("RGBA", (*black.split(), a))
            self._pet_sh_cache[key] = hit
        return hit

    def _update_pet_shadow(self):
        """반려동물이 나와 있는 동안만 그림자 창을 갱신 (약 15fps로 제한)."""
        if self.shadow is None or self.shadow_img is None:
            return
        drawn = self._pet_drawn
        now = time.time()
        if not drawn:
            if self._pet_sh_on:                  # 원래 그림자로 되돌린다
                self.shadow.set_image(self._shadow_base or self.shadow_img)
                self._pet_sh_on = False
            return
        if now - self._pet_sh_t < 0.065:
            return
        self._pet_sh_t = now
        comp = (self._shadow_base or self.shadow_img).copy()
        b, sp = self.PET_BLUR, SHADOW_PAD
        for name, dy, x, y in drawn:
            comp.alpha_composite(self._pet_shadow_pil(name, dy),
                                 (round(x) + sp - b, round(y) + sp - b))
        self.shadow.set_image(comp)
        self._pet_sh_on = True

    def _draw_pet(self, now):
        """책상 뒤에서 뿅 — 올라와 빤히 보다가 쏙 들어간다."""
        if not (self.fun and self.pet_t0):
            return
        c = self.canvas
        for name, delay in self.pet_cast:
            t = now - self.pet_t0 - delay
            if t < 0:
                continue
            if t < self.PET_RISE:
                f = t / self.PET_RISE
            elif t < self.PET_RISE + self.PET_HOLD:
                f = 1.0
            else:
                f = max(0.0, 1.0 - (t - self.PET_RISE - self.PET_HOLD) / self.PET_FALL)
            if f <= 0:
                continue
            f = f * f * (3 - 2 * f)                     # 부드럽게
            x, y = self._pet_xy[name]
            y += self.oy
            if f >= 1.0:                                # 빤히 보는 동안 살짝 들썩
                bob = math.sin((now + delay * 3) * 2.4) * 2.0
                c.create_image(x, y - bob, image=self._pet_img(name, 0),
                               anchor="nw")
                self._pet_drawn.append((name, 0, x, y - bob))
            else:
                dy = round(self._pet_hide.get(name, 0) * (1 - f) / 3) * 3
                c.create_image(x, y + dy, image=self._pet_img(name, dy),
                               anchor="nw")
                self._pet_drawn.append((name, dy, x, y + dy))


    def _draw_hat(self, yo):
        """축하용 고깔모자 (hat.png 있으면 사용, 없으면 임시 도형)."""
        if not (self.fun and time.time() < self.hat_until):
            return
        c = self.canvas
        name = "head" if self.has.get("head") else "body_open"
        if name not in self._pil_cache:
            return
        top = self._pos(name)[1] + yo
        bb = self._pil_cache[name].split()[3].getbbox()
        if bb:                          # 이미지 여백 제외한 실제 머리 꼭대기
            top += bb[1]
        dx, dy = self.cfg.get("hat_pos", [-44, 44])
        hx = self.card_cx + dx          # 살짝 비껴 씌워 말풍선을 안 가리게
        hat = self.im.get("hat")
        if hat is not None:
            c.create_image(hx, top + dy, image=hat, anchor="s")
            return
        c.create_polygon(hx - 19, top + 30, hx, top - 6, hx + 19, top + 30,
                         fill="#ffb3c9", outline="#e07a9c", width=2)
        c.create_oval(hx - 6, top - 16, hx + 6, top - 4,
                      fill="#fff0a8", outline="#e0b84a", width=2)

    def _draw_particles(self):
        c = self.canvas
        for x, y, _vx, _vy, col, _life in self.particles:
            c.create_rectangle(x - 3, y - 2, x + 3, y + 2, fill=col, outline="")

    @staticmethod
    def _bubble_pts(x0, y0, x1, y1, r, tx, tw, th):
        """둥근 사각형 + 아래쪽 V자 꼬리를 한 붓으로 이은 점 목록."""
        pts = []

        def arc(cx, cy, a0, a1, steps=6):
            for i in range(steps + 1):
                a = math.radians(a0 + (a1 - a0) * i / steps)
                pts.extend((cx + math.cos(a) * r, cy + math.sin(a) * r))

        arc(x1 - r, y0 + r, -90, 0)                 # 우상
        arc(x1 - r, y1 - r, 0, 90)                  # 우하
        pts.extend((tx + tw / 2, y1))               # 꼬리 시작
        pts.extend((tx - tw * 0.18, y1 + th))       # 꼬리 끝
        pts.extend((tx - tw / 2, y1))
        arc(x0 + r, y1 - r, 90, 180)                # 좌하
        arc(x0 + r, y0 + r, 180, 270)               # 좌상
        return pts

    def _draw_bubble(self, yo):
        """머리 위 말풍선 — 둥근 모서리 + 아래 V자 꼬리."""
        if not (self.can_talk and self.bubble):
            return
        text = self.bubble[0]
        c, cd = self.canvas, self.card
        # 말풍선은 카드와 달리 크기가 고정이 아니라, 글자에 맞춰 상자가 늘어난다.
        # 그래서 글자 크기 설정을 그대로 따라도 겹칠 일이 없다. 다만 창보다
        # 넓어지면 안 되니 그 선에서만 줄인다.
        font = self._fit(text, 9, self.W - 46)
        w = max(self._mw(text, font) + 34, 74)
        h = max(36, self._mh(font) + 20)
        cx = self.card_cx
        if time.time() < self.hat_until:      # 고깔모자를 가리지 않게 옆으로
            cx += 42
        cx = min(max(cx, w / 2 + 4), self.W - w / 2 - 4)   # 창 밖으로 안 나가게
        top = self._pos("head" if self.has.get("head") else "body_open")[1] + yo
        # 카드와 겹치지 않게 카드 아래로 (머리 위쪽에 걸침)
        card_bottom = self._card_geom()["y1"] if self.timer_on else self.oy
        by = max(top + 10, card_bottom + 40)
        x0, x1 = cx - w / 2, cx + w / 2
        pts = self._bubble_pts(x0, by - h, x1, by, 13, cx + 4, 17, 13)
        c.create_polygon([p + 2 for p in pts], fill="#e6e2e8", outline="")
        c.create_polygon(pts, fill="#ffffff", outline=cd["border"], width=2)
        c.create_text(cx, by - h / 2, text=text, font=font, fill=cd["text"])


    def _end_workday(self):
        """캐릭터 쪽에서 누른 작업 종료 — 기존 타이머에도 알려 기록으로 남긴다.

        '혼자 측정 중'이었다면 그동안 캐릭터가 잰 시간을 함께 넘긴다. 기존
        타이머는 그 시간을 모르기 때문에, 안 넘기면 그만큼이 통째로 빠진다.
        명령 파일은 기존 타이머가 읽어 갈 때까지 남아 있으므로, 지금 꺼져
        있어도 다음에 켜질 때 기록된다.
        """
        if self.ws_path is not None:
            solo = (max(0, int(self.work_secs - self._solo_from))
                    if self._ws_lost else 0)
            path = os.path.join(os.path.dirname(self.ws_path), ".mascot_cmd")
            try:
                with open(path, "w", encoding="utf-8") as fp:
                    json.dump({"cmd": "end", "solo_secs": solo,
                               "ts": time.time()}, fp)
            except Exception:
                self._log_error("end_cmd")
        self._celebrate()

    # ── 제스처 ───────────────────────────────────────────────────────────
    # 파츠를 새로 그리지 않고, 이미 있는 것들을 옮기고 돌려서 만든 동작들.
    # 움직일 수 있는 것은 머리(목을 축으로 회전 + 상하), 몸 전체(상하),
    # 그리고 두 손(늘어나는 팔이 따라온다)뿐이라 이 넷의 조합으로 짠다.
    GESTURES = {"wave": 2.0, "clap": 1.9, "nod": 1.2,
                "shake": 1.3, "stretch": 3.0, "groove": 3.6,
                "yawn": 2.8, "doze": 3.0, "think": 3.6, "startle": 1.1,
                "cheer": 2.4, "sway": 3.8}
    # 아래 여섯은 config의 "gestures_plus"를 켠 캐릭터에서만 나온다.
    GEST_PLUS = ("yawn", "doze", "think", "startle", "cheer", "sway")
    STRETCH_EVERY = 20 * 60      # 기지개 간격 기본값 (환경설정에서 바꾼다)
    # 환경설정에서 고를 수 있는 간격. 사람마다 집중 리듬이 달라 넓게 뒀다.
    STRETCH_CHOICES = ("끄기", "10분마다", "20분마다", "30분마다",
                       "45분마다", "60분마다", "90분마다")
    # 기지개를 켜며 하는 말. 캐릭터별로 config의 "stretch_talk"로 덮어쓴다.
    STRETCH_TALK = ("같이 쭉 펴 볼까요?", "어깨 한 번 풀어요.",
                    "잠깐 기지개 켜요.", "허리도 한 번 펴 봐요.")
    # 박수 자세 (캔버스 px 기준). 팔을 아래에서 위로 올려 붙이는 모양이
    # 되도록 어깨를 몸 아래쪽에 두고, 손은 턱 바로 밑에서 만나게 한다.
    CLAP_SWING = 26.0            # 손끝이 벌어지는 각도(도)
    CLAP_SHY = 22.0              # 박수용 어깨를 얼마나 내릴지 (작을수록 위)
    CLAP_LEN = 0.95              # 박수에서 쓰는 팔 길이 (원래 길이 대비)
    WAVE_SHY = -8.0              # 손 흔들 때 어깨를 얼마나 올릴지
    STRETCH_SHY = -22.0          # 기지개에서 어깨 높이 (작을수록 위)

    def _gest_start(self, name, force=False):
        """동작을 시작한다. 이미 하고 있으면 무시 — 겹치면 손이 튄다."""
        if not self.gestures_on or name not in self.GESTURES:
            return
        if name in self.GEST_PLUS and not self.cfg.get("gestures_plus"):
            return
        now = time.time()
        if not force and self.gest is not None \
                and now < self.gest_t0 + self.gest_dur:
            return
        self.gest, self.gest_t0 = name, now
        self.gest_dur = self.GESTURES[name]
        # 프레임마다 지워야 하는 값은 여기서 되돌린다. 자세 계산 안에서만
        # 만지면, 그 구역이 꺼졌을 때 마지막 값이 남아 자세가 굳는다.
        self._doze_woke = False
        if name == "yawn":
            self._safe("fx", self._spawn_note, now, "yawn")
        elif name == "startle":
            self._safe("fx", self._spawn_note, now, "bang")
        elif name == "cheer":
            self._note_left = random.randint(2, 3)
            self._note_next = now + 0.25
        elif name == "think":
            self._note_left = random.randint(1, 2)
            self._note_next = now + 0.5
            if self.can_talk and self.bubble is None:
                self._say("...", 2.6)
        if name == "groove":              # 음표는 두세 개만 — 많으면 지저분하다
            self._note_left = random.randint(2, 3)
            self._note_next = now + 0.35
        elif (name == "stretch" and self.can_talk and self.bubble is None
                and not self.stretch_pending):
            pool = self.cfg.get("stretch_talk") or self.STRETCH_TALK
            self._say(random.choice(list(pool)), 4.5)

    def _gest_tick(self, now, sleeping):
        """이번 프레임의 머리·몸·손 이동량을 정한다 (draw 맨 앞에서 호출)."""
        self._g_dy = self._g_hdy = self._g_tilt = 0.0
        self._g_hands = None
        self._g_eyes_shut = self._g_smile = False
        if not self.gestures_on:
            return
        # 그리거나 타자 치는 중에도 몸짓은 끝까지 한다. 팔이 잠깐 펜을
        # 놓더라도 그린 획 수와 펜 소리는 _track_pen이 계속 센다.
        if sleeping:
            self.gest = None
            return
        if self.gest is not None and now >= self.gest_t0 + self.gest_dur:
            self.gest = None
        self._gest_schedule(now)
        if self.gest is None:
            return
        try:
            self._gest_pose(now)
        except Exception:
            self.gest = None
            self._g_dy = self._g_hdy = self._g_tilt = 0.0
            self._g_hands = None
            self._g_eyes_shut = self._g_smile = False
            self._log_error("gesture")

    NOTE_STEPS = 7               # 파티클이 사라지기까지의 단계 수

    def _fx_cloud(self, size, color="#8f8f97", lobes=5):
        """하품 구름 — 덩어리를 합친 실루엣의 바깥 테두리만 남긴다.

        호를 여러 개 겹쳐 그리면 안쪽 선까지 남아 별처럼 보인다. 그래서
        실루엣을 만든 뒤 한 겹 깎아내 그 차이(테두리)만 쓰고, 덩어리가
        만나는 오목한 자리에 작은 구멍을 뚫어 손그림 같은 틈을 낸다.
        """
        from PIL import ImageChops, ImageDraw, ImageFilter
        n = int(size) + 4
        lw = max(2, round(size * 0.062))
        c = n * 0.5
        rr = n * 0.26
        dd = rr * 0.95
        sil = Image.new("L", (n, n), 0)
        sd = ImageDraw.Draw(sil)
        sd.ellipse([c - dd, c - dd, c + dd, c + dd], fill=255)  # 가운데 구멍 방지
        for k in range(lobes):
            a = math.radians(-90 + k * (360.0 / lobes))
            lx, ly = c + dd * math.cos(a), c + dd * math.sin(a)
            sd.ellipse([lx - rr, ly - rr, lx + rr, ly + rr], fill=255)
        ring = ImageChops.subtract(sil, sil.filter(ImageFilter.MinFilter(2 * lw + 1)))
        half = math.radians(180.0 / lobes)
        v = rr * rr - (dd * math.sin(half)) ** 2
        if v > 0:
            dn = dd * math.cos(half) + math.sqrt(v)
            gd = ImageDraw.Draw(ring)
            for k in range(lobes):
                a = math.radians(-90 + 180.0 / lobes + k * (360.0 / lobes))
                gx, gy = c + dn * math.cos(a), c + dn * math.sin(a)
                g = lw * 0.9
                gd.ellipse([gx - g, gy - g, gx + g, gy + g], fill=0)
        out = Image.new("RGBA", (n, n), (0, 0, 0, 0))
        out.paste(Image.new("RGBA", (n, n), color), (0, 0), ring)
        return out

    def _build_notes(self):
        """머리 위로 떠오르는 작은 그림들 — 음표·하트·땀·물음표·반짝임·느낌표.

        글꼴에 기대지 않고 도형으로 그린다 — 맥에서도 같은 모양. 색상키 창에서는
        반투명이 그대로 안 나온다(반투명 픽셀이 배경색과 섞여 거뭇해진다).
        그래서 옅어지는 대신 픽셀을 점점 솎아내 사라지게 한다.
        """
        self.fx_imgs = {}
        try:
            from PIL import ImageDraw, ImageFilter
            h = max(20, round(self.W * 0.135))
            col = self.card.get("fill", "#f2a7c5")
            st = max(2, round(h * 0.085))          # 기둥 굵기
            rx, ry = h * 0.21, h * 0.165           # 음표 머리 반지름

            def head(d, cx, cy):
                d.ellipse([cx - rx, cy - ry, cx + rx, cy + ry], fill=col)

            def stem(d, x, y0, y1):
                d.rectangle([x - st, y0, x, y1], fill=col)

            notes = []
            # ① 홑음표 — 머리 + 기둥 + 휘어진 깃발
            w0 = round(h * 0.70)

            def draw0(d):
                cx, cy = rx + 1, h - ry - 1
                top = h * 0.10
                head(d, cx, cy)
                stem(d, cx + rx, top, cy)
                d.polygon([(cx + rx, top), (cx + rx + h * 0.26, top + h * 0.16),
                           (cx + rx + h * 0.24, top + h * 0.44),
                           (cx + rx + h * 0.10, top + h * 0.30),
                           (cx + rx + h * 0.13, top + h * 0.17),
                           (cx + rx, top + h * 0.24)], fill=col)
            notes.append((w0, draw0))
            # ② 두 음표 — 기둥 위를 굵은 대로 이었다
            w1 = round(h * 1.05)

            def draw1(d):
                ax, ay = rx + 1, h - ry - 1
                bx, by = w1 - rx - 1, h - ry - h * 0.16
                ta, tb = h * 0.20, h * 0.06
                head(d, ax, ay)
                head(d, bx, by)
                stem(d, ax + rx, ta, ay)
                stem(d, bx + rx, tb, by)
                d.polygon([(ax + rx - st, ta), (bx + rx, tb),
                           (bx + rx, tb + h * 0.20),
                           (ax + rx - st, ta + h * 0.20)], fill=col)
            notes.append((w1, draw1))

            # ③ 하트
            wh = round(h * 0.92)

            def drawh(d, c="#ff8fb0"):
                r = wh * 0.26
                d.ellipse([0, h * 0.14, 2 * r, h * 0.14 + 2 * r], fill=c)
                d.ellipse([wh - 2 * r, h * 0.14, wh, h * 0.14 + 2 * r], fill=c)
                d.polygon([(1, h * 0.34), (wh - 1, h * 0.34),
                           (wh / 2, h * 0.97)], fill=c)

            # ④ 땀방울
            ws = max(6, round(h * 0.50))

            def draws(d, c="#7fc4f2"):
                d.ellipse([0, h * 0.40, ws, h * 0.40 + ws], fill=c)
                d.polygon([(ws / 2, h * 0.04), (ws * 0.06, h * 0.62),
                           (ws * 0.94, h * 0.62)], fill=c)

            # ⑤ 물음표
            wq = max(8, round(h * 0.66))

            def drawq(d, c=col):
                lw = max(2, round(h * 0.13))
                d.arc([lw / 2, h * 0.04, wq - lw / 2, h * 0.52],
                      150, 30, fill=c, width=lw)
                d.line([(wq * 0.74, h * 0.40), (wq * 0.50, h * 0.64)],
                       fill=c, width=lw)
                d.ellipse([wq * 0.5 - lw * 0.9, h * 0.76,
                           wq * 0.5 + lw * 0.9, h * 0.76 + lw * 1.8], fill=c)

            # ⑥ 반짝임 (네 갈래 별)
            wk = max(8, round(h * 0.78))

            def drawk(d, c="#ffcf5e"):
                cx, cy = wk / 2, h / 2
                a = min(wk, h) * 0.46
                b = a * 0.26
                d.polygon([(cx, cy - a), (cx + b, cy - b), (cx + a, cy),
                           (cx + b, cy + b), (cx, cy + a), (cx - b, cy + b),
                           (cx - a, cy), (cx - b, cy - b)], fill=c)

            # ⑦ 느낌표
            wb = max(5, round(h * 0.34))

            def drawb(d, c="#ff9770"):
                d.polygon([(wb * 0.10, h * 0.04), (wb * 0.90, h * 0.04),
                           (wb * 0.68, h * 0.62), (wb * 0.32, h * 0.62)],
                          fill=c)
                d.ellipse([wb * 0.12, h * 0.74,
                           wb * 0.88, h * 0.74 + wb * 0.76], fill=c)

            # ⑧ 하품 구름 — '하품 중'을 알리는 표시라 다른 것보다 크게.
            hy = wy = round(h * 1.5)
            cloud = self._fx_cloud(hy)

            groups = {"note": notes, "heart": [(wh, drawh)],
                      "yawn": [(wy, cloud, hy)],
                      "sweat": [(ws, draws)], "question": [(wq, drawq)],
                      "spark": [(wk, drawk)], "bang": [(wb, drawb)]}
            for kind, group in groups.items():
                made = []
                for spec in group:
                    w, fn = spec[0], spec[1]
                    kh = spec[2] if len(spec) > 2 else h   # 종류마다 높이가 다를 수 있다
                    base = Image.new("RGBA", (int(w) + 4, int(kh) + 4),
                                     (0, 0, 0, 0))
                    if isinstance(fn, Image.Image):   # 미리 만들어 둔 그림
                        base.alpha_composite(fn)
                    else:
                        fn(ImageDraw.Draw(base))
                    # 어떤 배경에서도 보이게 흰 테두리를 한 겹 두른다
                    rim = base.split()[3].filter(ImageFilter.MaxFilter(3))
                    out = Image.new("RGBA", base.size, (255, 255, 255, 0))
                    out.putalpha(rim)
                    out.alpha_composite(base)
                    lv = []
                    for k in range(self.NOTE_STEPS):
                        keep = 1.0 - k / float(self.NOTE_STEPS)
                        im = out.copy()
                        a = im.split()[3].load()
                        px = im.load()
                        for y in range(im.height):
                            for x in range(im.width):
                                if a[x, y] and random.random() > keep:
                                    px[x, y] = (0, 0, 0, 0)
                        lv.append(ImageTk.PhotoImage(self._hard(im)))
                    made.append(lv)
                self.fx_imgs[kind] = made
        except Exception:
            self.fx_imgs = {}
            self._log_error("notes")

    def _spawn_note(self, now, kind="note"):
        """머리 위로 작은 그림 하나를 푱 하고 띄운다."""
        lvs = self.fx_imgs.get(kind) or self.fx_imgs.get("note")
        if not lvs:
            return
        hx0, hy0, hx1, hy1 = self._head_box
        side = random.choice((-1, 1))
        x = (hx0 + hx1) / 2 + side * (hx1 - hx0) * random.uniform(0.22, 0.44)
        y = self.oy + hy0 + (hy1 - hy0) * random.uniform(0.05, 0.22)
        life = random.randint(34, 52)
        # 그림 목록을 그대로 들고 있는다 — 종류가 늘어도 번호가 꼬이지 않는다.
        self.notes.append([x, y, side * random.uniform(0.25, 0.7),
                           random.uniform(1.1, 1.8),
                           random.choice(lvs), life, life])

    def _step_notes(self):
        alive = []
        for n in self.notes:
            n[0] += n[2]
            n[1] -= n[3]
            n[2] *= 0.985
            n[5] -= 1
            if n[5] > 0 and n[1] > -20:
                alive.append(n)
        self.notes = alive

    def _draw_notes(self):
        for n in self.notes:
            lv = n[4]
            i = min(len(lv) - 1, int((1.0 - n[5] / max(n[6], 1)) * len(lv)))
            self.canvas.create_image(n[0], n[1], image=lv[i], anchor="center")

    def _greet_tick(self, now, state):
        """작업이 시작돼 타이머 초가 흐르기 시작하면 손을 흔들어 인사한다.

        잠깐 쉬었다 돌아올 때마다 하면 성가시므로 쿨다운을 둔다.
        """
        if state == self._last_state:
            return
        if state == "work" and now >= self.gest_wave_next:
            self.gest_wave_next = now + 600
            self._gest_start("wave")
        self._last_state = state

    # 알림을 끄고 나서 하는 말. config의 "stretch_done_talk"로 덮어쓴다.
    STRETCH_DONE = ("시원하다!", "좀 낫네요.", "개운해요.")
    HINT_SUFFIX = " (눌러 주세요)"     # config의 "stretch_hint_suffix"로 덮어쓴다
    TAP_HINT_AT = 30.0           # 이만큼 안 누르면 누르라는 표시가 뜬다(초)
    TAP_CARD_AT = 60.0           # 이만큼 안 누르면 카드 문구까지 바뀐다(초)

    def _stretch_secs(self):
        """스트레칭 알림 간격(초). 0이면 알리지 않는다.

        환경설정에는 '30분마다'처럼 사람이 읽는 말로 저장돼 있어 숫자만 뽑는다.
        """
        raw = str(self.us.get("stretch_every", "") or "")
        if raw.startswith("끄"):
            return 0
        num = "".join(ch for ch in raw if ch.isdigit())
        if not num:
            return self.STRETCH_EVERY
        return max(5, min(180, int(num))) * 60

    def _stretch_raise(self, now):
        """스트레칭 알림을 띄운다. 누를 때까지 안 꺼진다."""
        if self.stretch_pending:
            return                          # 이미 떠 있으면 겹쳐 쌓지 않는다
        self.stretch_pending = True
        self.stretch_shown = 0.0
        self.stretch_replay = 0.0
        self._stretch_last = now
        line = random.choice(list(self.cfg.get("stretch_talk")
                                  or self.STRETCH_TALK))
        # 처음 몇 번만 '눌러 주세요'를 붙인다. 매번 붙이면 잔소리가 된다.
        left = int(self.us.get("stretch_hint", 3) or 0)
        if left > 0:
            self.us["stretch_hint"] = left - 1
            self._save_settings()
            line += self.cfg.get("stretch_hint_suffix") or self.HINT_SUFFIX
        self._stretch_line = line
        self._gest_start("startle")       # 알림이 뜰 때 한 번 움찔

    def _stretch_done(self, now):
        """캐릭터를 눌러 알림을 껐다."""
        self.stretch_pending = False
        self.stretch_shown = 0.0
        self.gest = None
        self.bubble = None
        pool = self.cfg.get("stretch_done_talk") or self.STRETCH_DONE
        self._say(random.choice(list(pool)), 3.0)
        self.smile_until = now + 3.0
        self._safe("burst", self._burst, 10, 26)

    def _on_screen(self):
        """캐릭터가 실제로 보이는가 — 전체화면 프로그램에 덮였는지 확인.

        안 보이는 동안 알림 시간이 흐르면, 나중에 화면을 나왔을 때 한참 전
        알림이 그대로 떠 있게 된다. 그래서 보이는 동안만 시간을 센다.
        """
        if not IS_WIN or self.us.get("topmost", True):
            return True                     # 항상 위면 덮일 일이 없다
        try:
            u = ctypes.windll.user32
            fg = u.GetForegroundWindow()
            if not fg or fg == self._main_hwnd:
                return True
            r = (ctypes.c_long * 4)()        # left, top, right, bottom
            u.GetWindowRect(fg, ctypes.byref(r))
            x, y = self.root.winfo_rootx(), self.root.winfo_rooty()
            return not (r[0] <= x and r[1] <= y
                        and r[2] >= x + self.W and r[3] >= y + self.H)
        except Exception:
            return True

    def _stretch_tick(self, now, sleeping):
        """알림이 떠 있는 동안 말풍선을 붙잡고 기지개를 되풀이한다."""
        self._stretch_hover = False
        if not self.stretch_pending:
            return
        dt = min(max(now - self._stretch_last, 0.0), 1.0)
        self._stretch_last = now
        if sleeping or not self._on_screen():
            return          # 자리를 비웠거나 가려져 있으면 시간도 연출도 멈춘다
        self.stretch_shown += dt
        # 사라지지 않게 계속 붙잡아 두되, 다른 말이 떠 있으면 기다린다.
        # 안 그러면 할 일 완료 같은 반응이 바로 덮여 안 보인다.
        if self.bubble is None or self.bubble[0] == self._stretch_line:
            self._say(self._stretch_line, 3.0)
        if self.gest is None and now >= self.stretch_replay:
            # 쉬지 않고 이어 붙이면 부산스러워서 한 박자 쉬었다 다시 켠다
            self.stretch_replay = now + self.GESTURES["stretch"] + 4.5
            self._gest_start("stretch", force=True)
        cx, cy = cursor_pos()
        x, y = self.root.winfo_rootx(), self.root.winfo_rooty()
        self._stretch_hover = (x <= cx <= x + self.W
                               and y + self.oy <= cy <= y + self.H)

    def _draw_tap_ring(self, now):
        """여기를 누르라는 표시 — 물결처럼 원이 퍼진다.

        색상키 창이라 서서히 옅어지게는 못 만든다. 대신 퍼질수록 선을 얇게
        해서 사라지는 것처럼 보이게 한다.
        """
        if not (self.stretch_pending and self.stretch_shown >= self.TAP_HINT_AT):
            return
        c = self.canvas
        col = self.card.get("text", "#7a6a9e")   # 흰 몸통 위에서도 보이게 진한 색
        hx0, hy0, hx1, hy1 = self._head_box
        cx = (hx0 + hx1) / 2
        cy = self.oy + hy1 - (hy1 - hy0) * 0.06
        speed = 1.7 if self._stretch_hover else 0.95   # 커서를 올리면 빨라진다
        for k in range(2):
            p = ((now * speed) + k * 0.5) % 1.0
            r = 11 + 32 * p
            w = max(1, round(4.0 * (1.0 - p)))
            c.create_oval(cx - r, cy - r, cx + r, cy + r, outline=col, width=w)
        c.create_oval(cx - 5, cy - 5, cx + 5, cy + 5, fill=col, outline="")

    def _gest_schedule(self, now):
        """스스로 나오는 몸짓 — 리듬 타기와 기지개."""
        if self.gest_groove_next == 0.0:      # 켜자마자 움직이면 놀란다
            self.gest_groove_next = now + random.uniform(120, 300)
        elif now >= self.gest_groove_next:
            self.gest_groove_next = now + random.uniform(480, 900)
            self._gest_start("groove")        # 1시간에 네댓 번
        self._gest_extra(now)
        if not self.timer_on:
            return
        every = self._stretch_secs()
        if not every:                          # 환경설정에서 껐다
            self.gest_stretch_next = 0.0
            if self.stretch_pending:           # 떠 있던 알림도 조용히 거둔다
                self.stretch_pending = False
                self.gest = None
                self.bubble = None
            return
        if self.gest_stretch_next == 0.0:
            self.gest_stretch_next = now + every
        elif self.gest_stretch_next > now + every:
            self.gest_stretch_next = now + every   # 간격을 줄이면 바로 반영
        elif now >= self.gest_stretch_next:
            self.gest_stretch_next = now + every
            self._stretch_raise(now)           # 정해 둔 간격마다

    def _gest_extra(self, now):
        """새 몸짓의 방아쇠 — 하품·꾸벅·생각. (움찔은 놀랄 일이 있을 때만)

        타이머 상태(_last_state)를 보고 어울리는 때에만 낸다. 처음 켠 직후에
        바로 나오면 놀라므로 첫 시각은 넉넉히 뒤로 잡는다.
        """
        if not self.cfg.get("gestures_plus"):
            return
        state = self._last_state
        if self._yawn_next == 0.0:
            self._yawn_next = now + random.uniform(600, 1200)
            self._doze_next = now + random.uniform(420, 900)
            self._think_next = now + random.uniform(300, 700)
            self._sway_next = now + random.uniform(300, 700)
            self._heart_next = now + random.uniform(240, 480)
            return
        if state == "work" and now >= self._heart_next:
            # 작업 중에는 흐뭇하게 지켜본다는 뜻으로 하트를 종종 띄운다
            self._heart_next = now + random.uniform(540, 660)
            for _ in range(random.randint(1, 2)):
                self._spawn_note(now, "heart")
        if now >= self._yawn_next:
            self._yawn_next = now + random.uniform(900, 1800)
            hour = time.localtime(now).tm_hour
            # 새벽이거나 오래 앉아 있었을 때만 — 아무 때나 하면 뜬금없다
            if 0 <= hour < 6 or self._shown_secs() > 3 * 3600:
                self._gest_start("yawn")
                return
        if state != "work" and now >= self._doze_next:
            self._doze_next = now + random.uniform(420, 900)
            self._gest_start("doze")
            return
        if state in ("idle", "other") and now >= self._think_next:
            self._think_next = now + random.uniform(300, 700)
            self._gest_start("think")
            return
        if now >= self._sway_next:
            self._sway_next = now + random.uniform(420, 900)
            self._gest_start("sway")

    def _talk_gesture(self, text):
        """대사에 어울리는 고개짓 — 부정하는 말이면 도리도리, 아니면 끄덕임."""
        t = str(text)
        if any(k in t for k in ("아니", "몰라", "싫", "안 ", "못 ", "말고",
                                "글쎄", "없어", "없어요")):
            return "shake"
        if any(k in t for k in ("좋", "그래", "맞", "하자", "가자", "해야",
                                "!", "네", "응")):
            return "nod"
        return random.choice(("nod", "shake"))

    def _gest_pose(self, now):
        """진행도(0~1)에 따라 이번 프레임의 자세를 계산한다.

        손 이동량은 PSD 캔버스 픽셀로 적고 마지막에 표시 배율(s)을 곱한다.
        그래야 캐릭터를 크게/작게 해도 같은 자세가 나온다.
        """
        p = min(1.0, max(0.0, (now - self.gest_t0) / max(self.gest_dur, 0.01)))
        ease = math.sin(p * math.pi)          # 시작과 끝에서 0 — 튀지 않게
        tm = self._tilt_max or 0.0
        s = self.s
        g = self.gest
        if g in self.GEST_PLUS:
            self._pose_plus(g, p, now, s, tm)
            return
        if g == "nod":                        # 끄덕끄덕 — 머리만 아래위로
            self._g_hdy = abs(math.sin(p * math.pi * 4)) * 18 * s * ease
            return
        if g == "shake":                      # 도리도리 — 목을 축으로 좌우
            self._g_tilt = math.sin(p * math.pi * 6) * tm * ease
            return
        if g == "groove":                     # 리듬 타기 — 머리 기울기 + 통통
            # 손은 건드리지 않는다. 제스처 중의 손은 머리 위에 그려지는데,
            # 제자리 근처에서 그러면 평소 머리에 가려 있던 부분이 갑자기
            # 드러나 툭 튀어 보인다. 크게 움직이는 동작에서만 손을 쓴다.
            beat = math.sin(p * math.pi * 4)
            self._g_tilt = beat * tm * 0.85 * ease
            self._g_dy = -abs(math.sin(p * math.pi * 8)) * 5 * ease
            self._g_smile = True
            if self._note_left > 0 and now >= self._note_next:
                self._note_left -= 1
                self._note_next = now + random.uniform(0.65, 1.0)
                self._spawn_note(now)
            return
        if g == "wave":                       # 손 흔들기 — 손끝을 위아래로
            # 오른팔 손끝만 까딱까딱. 펜 쥔 손은 손끝에 붙어 함께 따라온다.
            osc = math.sin(p * math.pi * 6)
            self._g_hands = {"r": (-25 * s * ease,
                                   (-90 + 55 * osc) * s * ease),
                             "sh_dy": self.WAVE_SHY}
            self._g_tilt = -tm * 0.45 * ease
            return
        if g == "stretch":
            # 기지개 — 두 팔을 위로 쭉 올려 길게 뻗은 채로 버티다가, 팔 끝이
            # 바르르 떨리고, 천천히 내려온다. 올라가고 내려오는 구간만
            # 부드럽게 하고 가운데는 그대로 붙잡아 둔다(그냥 사인 곡선으로
            # 하면 최대 자세가 한순간이라 버티는 느낌이 안 난다).
            if p < 0.26:
                u = p / 0.26
            elif p < 0.74:
                u = 1.0
            else:
                u = max(0.0, (1.0 - p) / 0.26)
            u = math.sin(min(1.0, u) * math.pi / 2)
            tre = (math.sin((p - 0.30) / 0.42 * math.pi)
                   if 0.30 < p < 0.72 else 0.0)
            jx = math.sin(now * 52.0) * 11 * s * tre
            jy = math.sin(now * 47.0 + 1.1) * 9 * s * tre
            self._g_hands = {"r": (-110 * s * u + jx, -260 * s * u + jy),
                             "l": (110 * s * u - jx, -260 * s * u + jy),
                             "sh_dy": self.STRETCH_SHY}
            self._g_dy = -7 * u
            self._g_eyes_shut = u > 0.25      # 시원하게 눈을 감는다
            return
        if g == "clap":
            # 박수 — 어깨(팔이 몸에 붙는 자리)를 축으로 고정하고 팔 위쪽만
            # 호를 그린다. 팔 길이는 원래대로 두어야 손이 눌려 보이지 않는다.
            # 두 손이 만나는 자리는 어깨 간격과 팔 길이로 정해지는 삼각형의
            # 꼭짓점이라, 자연히 어깨보다 위가 된다.
            op = abs(math.sin(p * math.pi * 7))   # 0 = 맞붙음, 1 = 벌어짐
            sr = self._gest_shoulder(self.arm_top, self.CLAP_SHY)
            sl = self._gest_shoulder(self.armk_top, self.CLAP_SHY)
            cx, cy = (sr[0] + sl[0]) / 2.0, (sr[1] + sl[1]) / 2.0
            ux, uy = sl[0] - sr[0], sl[1] - sr[1]
            span = math.hypot(ux, uy) or 1.0
            half = span / 2.0
            L = max(math.hypot(*self._arm_nat) * self.CLAP_LEN, half * 1.08)
            h = math.sqrt(max(L * L - half * half, 1.0))
            nx, ny = -uy / span, ux / span       # 어깨선의 수직 방향
            if ny > 0:
                nx, ny = -nx, -ny                # 위쪽으로
            meet = (cx + nx * h, cy + ny * h)
            out = {}
            for side, sh, rest in (("r", sr, self.arm_bottom),
                                   ("l", sl, self.armk_bottom)):
                # 벌어지는 방향 = 그 팔의 어깨가 있는 바깥쪽. 만나는 점이
                # 두 어깨의 한가운데라 '중심에서 멀어지는 쪽'으로 고르면
                # 양팔이 같은 방향으로 돌아 손이 벌어지지 않는다.
                want = 1.0 if sh[0] > cx else -1.0
                far = meet
                for d in (self.CLAP_SWING, -self.CLAP_SWING):
                    cand = _arc(sh, meet, d)
                    if (cand[0] - meet[0]) * want > 0:
                        far = cand
                        break
                # 올리고 내리는 과정은 보여주지 않는다. 시작하자마자 팔이
                # 올라가 있고 끝나면 툭 하고 제자리로 — 그래서 ease를 안 쓴다.
                tip = (meet[0] + (far[0] - meet[0]) * op,
                       meet[1] + (far[1] - meet[1]) * op)
                out[side] = (tip[0] - rest[0], tip[1] - rest[1])
            out["sh_dy"] = self.CLAP_SHY
            out["r_mirror"] = True               # 팔이 몸 안쪽을 향하게
            out["hide_pen"] = True               # 박수 칠 땐 펜을 놓는다
            self._g_hands = out
            self._g_hdy = -4.0
            return

    @staticmethod
    def _hold(p, rise, fall):
        """0에서 1로 올랐다가 붙잡아 두고 다시 0으로 — 정점을 버티는 곡선."""
        if p < rise:
            u = p / max(rise, 1e-6)
        elif p < fall:
            u = 1.0
        else:
            u = max(0.0, (1.0 - p) / max(1.0 - fall, 1e-6))
        return math.sin(min(1.0, u) * math.pi / 2)

    def _pose_plus(self, g, p, now, s, tm):
        """새로 넣은 넷 — 하품·꾸벅·생각·움찔."""
        if g == "yawn":
            # 하품 — 눈을 감고 고개를 살짝 든 채 한 손을 입가로 올린다.
            u = self._hold(p, 0.30, 0.72)
            self._g_eyes_shut = u > 0.2
            self._g_tilt = -tm * 0.45 * u
            self._g_hdy = -5 * s * u
            self._g_dy = -3 * u
            # 손이 크게 움직이는 동작이라 손을 써도 팔뿌리가 드러나지 않는다.
            self._g_hands = {"r": (-34 * s * u, -150 * s * u),
                             "sh_dy": 6.0, "hide_pen": True}
            return
        if g == "doze":
            # 꾸벅 — 고개가 점점 빨리 떨어졌다가 화들짝 들리며 부르르 떤다.
            if p < 0.72:
                u = (p / 0.72) ** 1.7
                self._g_eyes_shut = True
            else:
                k = (p - 0.72) / 0.28
                u = max(0.0, 1.0 - k * 2.4)
                self._g_tilt = math.sin(k * math.pi * 5) * tm * 0.5 * (1 - k)
                if not self._doze_woke:
                    self._doze_woke = True
                    self._spawn_note(now, "bang")
            self._g_hdy = 26 * s * u
            self._g_dy = 4 * u
            return
        if g == "think":
            # 턱 괴고 생각 — 한 손을 턱에 대고 고개를 기울인 채 멈춘다.
            u = self._hold(p, 0.22, 0.78)
            self._g_tilt = tm * 0.55 * u
            self._g_hdy = 3 * s * u
            self._g_hands = {"r": (-22 * s * u, -116 * s * u),
                             "sh_dy": 8.0, "hide_pen": True}
            if self._note_left > 0 and now >= self._note_next:
                self._note_left -= 1
                self._note_next = now + random.uniform(0.9, 1.4)
                self._spawn_note(now, "question")
            return
        if g == "cheer":
            # 만세 — 두 팔을 번쩍 들고 몸이 통통. 기지개와 달리 떨지 않는다.
            u = self._hold(p, 0.18, 0.76)
            self._g_dy = -10 * u - abs(math.sin(p * math.pi * 6)) * 5 * u
            self._g_tilt = math.sin(p * math.pi * 2) * tm * 0.30 * u
            self._g_smile = True
            self._g_hands = {"r": (-124 * s * u, -300 * s * u),
                             "l": (124 * s * u, -300 * s * u),
                             "sh_dy": -14.0, "hide_pen": True}
            if self._note_left > 0 and now >= self._note_next:
                self._note_left -= 1
                self._note_next = now + random.uniform(0.35, 0.6)
                self._spawn_note(now, "spark")
            return
        if g == "sway":
            # 좌우로 흔들기 — 리듬 타기보다 느리고 폭이 크다. 손은 쓰지 않는다
            # (제자리 근처에서 손을 쓰면 평소 머리에 가려 있던 팔이 드러난다).
            ease = math.sin(min(1.0, p * 3.0) * math.pi / 2) * \
                math.sin(min(1.0, (1.0 - p) * 3.0) * math.pi / 2)
            beat = math.sin(p * math.pi * 3)
            self._g_tilt = beat * tm * ease
            self._g_dy = -abs(beat) * 6 * ease
            self._g_hdy = -abs(beat) * 3 * ease
            return
        if g == "startle":
            # 움찔 — 짧게 튀어 올랐다가 떨림이 잦아든다.
            k = math.exp(-p * 4.0)
            self._g_dy = -15 * math.sin(min(1.0, p * 2.2) * math.pi) - 2 * k
            self._g_tilt = math.sin(p * math.pi * 9) * tm * 0.7 * k
            self._g_hdy = -6 * s * k

    def _gest_shoulder(self, top, dy=16.0):
        """제스처용 어깨 — 원래 접합점보다 몸 안쪽으로 묻어 둔 자리.

        팔을 위로 들면 어깨 쪽 둥근 끝이 몸 윤곽 밖으로 돌아나가면서 그 사이로
        머리카락과 배경이 비친다. 접합점을 몸 안에 넣어 두면 팔뿌리가 몸에
        덮여 틈이 생기지 않는다. dy로 위아래 위치도 동작마다 달리 잡는다.
        """
        s = self.s
        d = 1.0 if self.body_mid_x >= top[0] else -1.0
        return (top[0] + 34 * s * d, top[1] + dy * s)

    def _draw_gesture_arms(self, yo):
        """제스처 중의 두 팔. 어깨는 그대로 두고 손끝만 원하는 자리로 보낸다.

        '오른손'(펜 쥔 파츠)은 오른팔 손끝에 붙어 함께 움직인다 — 따로 돌리면
        팔에서 떨어져 보인다. 왼팔은 옮길 때만 늘여 그리고, 아니면 평소 자리에
        그대로 둔다(늘인 팔을 겹쳐 그리면 팔이 두 개로 보인다).
        """
        c = self.canvas
        g = self._g_hands or {}
        d4 = yo * 0.25
        ddx, ddy = g.get("r", (0.0, 0.0))
        sx, sy = self._gest_shoulder(self.arm_top, g.get("sh_dy", 16.0))
        hx, hy = self.arm_bottom[0] + ddx, self.arm_bottom[1] + ddy
        arm = self._stretched_arm(hx - sx, hy - sy,
                                  "rm" if g.get("r_mirror") else "r")
        if arm is not None:
            c.create_image(sx - arm[1][0], sy - arm[1][1] + d4,
                           image=arm[0], anchor="nw")
        if not g.get("hide_pen"):
            deg = self._arm_deg(hx - sx, hy - sy,
                                "rm" if g.get("r_mirror") else "r")
            if not self._pen_at_tip(hx, hy + d4, deg):
                px, py = self._pos("arm_pen")
                self._put("arm_pen", px + ddx, py + ddy + d4)

        hk = self.hop.get("arm_key")
        if "l" in g and "l" in self._arm_src:
            lx, ly = g["l"]
            sx2, sy2 = self._gest_shoulder(self.armk_top, g.get("sh_dy", 16.0))
            hx2, hy2 = self.armk_bottom[0] + lx, self.armk_bottom[1] + ly
            arm2 = self._stretched_arm(hx2 - sx2, hy2 - sy2, "l")
            if arm2 is not None:
                c.create_image(sx2 - arm2[1][0], sy2 - arm2[1][1] + d4,
                               image=arm2[0], anchor="nw")
        elif hk is not None:
            kx, ky = self._pos("arm_key")
            c.create_image(kx + self.arm_key_off[0] + hk["off"][0],
                           ky + self.arm_key_off[1] + hk["off"][1] + d4,
                           image=self._rotated_hop("arm_key", 0.0), anchor="nw")

    def _burst(self, n=24, spread=45):
        """카드 위로 색종이가 팡 터진다 (할 일 완료·기록 갱신 등 작은 축하용)."""
        cols = ["#ff9ec4", "#ffd479", "#9ad7ff", "#b8e986", "#c9a7ff", "#ffa9a9"]
        for _ in range(n):
            ang = random.uniform(-2.7, -0.45)
            spd = random.uniform(3.0, 7.0)
            self.particles.append([self.card_cx + random.uniform(-spread, spread),
                                   self.oy + 46,
                                   math.cos(ang) * spd, math.sin(ang) * spd,
                                   random.choice(cols), random.randint(35, 70)])

    def _celebrate(self):
        """작업 종료 — 고깔모자 + 폭죽 + 축하 말풍선, 잠시 뒤 브리핑."""
        now = time.time()
        self.celebrate_until = now + 4.0
        self.hat_until = now + 14.0
        self.smile_until = now + 5.0            # 말풍선이 떠 있는 동안 웃는 얼굴
        self._gest_start("clap", force=True)
        self.stretch_pending = False      # 일을 끝냈으니 알림도 내린다
        self._safe("history", self._hist_add)
        if self.cfg.get("reset_on_end"):  # 시간을 0으로 되돌린다
            self.zero_at = self.work_secs
            self._timer_save()
        self._reset_records()                   # 작업 종료 = 이번 '오늘'의 끝
        self._say("수고하셨습니다!", 5.0)
        cols = ["#ff9ec4", "#ffd479", "#9ad7ff", "#b8e986", "#c9a7ff", "#ffa9a9"]
        for _ in range(48):
            ang = random.uniform(-2.7, -0.45)
            spd = random.uniform(3.5, 8.5)
            self.particles.append([self.card_cx + random.uniform(-70, 70),
                                   self.oy + 46,
                                   math.cos(ang) * spd, math.sin(ang) * spd,
                                   random.choice(cols), random.randint(45, 85)])
        self.root.after(1500, self._open_briefing)

    def _open_briefing(self):
        """오늘의 작업 브리핑 팝업."""
        if getattr(self, "_brief_win", None) is not None \
                and self._brief_win.winfo_exists():
            self._brief_win.lift()
            return
        cd = self.card
        s = self.stat
        total = int(self._shown_secs())
        goal = max(float(self.us.get("goal_hours", 6)), 0.5) * 3600
        pct = min(int(total / goal * 100), 999)

        def hm(sec):
            sec = int(sec)
            return f"{sec // 3600}시간 {sec % 3600 // 60}분" if sec >= 3600 \
                else f"{sec // 60}분"

        def clock(ts):
            return time.strftime("%H:%M", time.localtime(ts)) if ts else "-"

        rows = [("총 작업 시간", hm(total)),
                ("목표 달성", f"{pct}%  (목표 {self.us.get('goal_hours')}h)"),
                ("최장 집중", hm(s.get("best", 0))),
                ("시작 · 마지막", f"{clock(s.get('first'))} – {clock(s.get('last'))}"),
                ("딴짓 / 휴식", f"{hm(s.get('other', 0))} / {hm(s.get('idle', 0))}"),
                ("키 입력", f"{int(s.get('keys', 0)):,}회"),
                ("그린 획", f"{int(s.get('strokes', 0)):,}획")]
        hs = self._hist_summary() if self.cfg.get("history") else None
        if hs:
            gap = total - hs["yday"]
            sign = "+" if gap >= 0 else "-"
            rows.append(("어제", hm(hs["yday"]) if hs["yday"] else "기록 없음"))
            if hs["yday"]:
                rows.append(("어제보다", f"{sign}{hm(abs(gap))}"))
            rows.append(("최근 7일", hm(hs["week"])))
            if hs["streak"] >= 2:
                rows.append(("연속", f"{hs['streak']}일째"))

        u = self._ui
        W, PAD, ROW = u(350), u(22), u(34)
        HEAD_H = u(100)
        body_h = ROW * len(rows) + u(20)
        H = u(22) + HEAD_H + u(22) + body_h + u(26) + u(42) + u(24)
        win = tk.Toplevel(self.root)
        self._brief_win = win
        win.title("오늘의 작업")
        win.attributes("-topmost", True)
        win.resizable(False, False)
        win.configure(bg=cd["panel"])
        cv = tk.Canvas(win, width=W, height=H, bg=cd["panel"],
                       highlightthickness=0)
        cv.pack()

        def rr(x0, y0, x1, y1, r, **kw):
            pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1,
                   x1 - r, y1, x0 + r, y1, x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]
            return cv.create_polygon(pts, smooth=True, **kw)

        y = u(22)
        rr(PAD, y, W - PAD, y + HEAD_H, u(18), fill=cd["soft"],
           outline=cd["border"], width=2)
        cv.create_text(W / 2, y + u(30), text="오늘도 수고하셨어요!",
                       font=self._uf(12, True), fill=cd["text"])
        cv.create_text(W / 2, y + u(54), text=hm(total) + " 작업했어요",
                       font=self._uf(9), fill=cd["sub"])
        # 캡쳐해서 모아 두면 나중에 어느 날 것인지 알아보기 어려워서 넣는다
        cv.create_text(W / 2, y + u(80),
                       text=f"{self.cfg.get('name', self.char)} · {self._session_day()}",
                       font=self._uf(8), fill=cd["sub"])
        y += HEAD_H + u(22)

        rr(PAD, y, W - PAD, y + body_h, u(16), fill="#ffffff",
           outline=cd["line"], width=1)
        ry = y + u(10) + ROW / 2
        for i, (k, v) in enumerate(rows):
            if i:
                cv.create_line(PAD + u(18), ry - ROW / 2, W - PAD - u(18), ry - ROW / 2,
                               fill=cd["line"])
            cv.create_text(PAD + u(18), ry, anchor="w", text=k,
                           font=self._uf(9), fill=cd["sub"])
            cv.create_text(W - PAD - u(18), ry, anchor="e", text=v,
                           font=self._uf(9, True), fill=cd["text"])
            ry += ROW
        y += body_h + u(26)

        def reset_and_close():
            self.work_secs = 0.0
            for k in ("work", "other", "idle", "best", "_run", "first", "last"):
                self.stat[k] = 0.0
            self.stat["keys"] = self.stat["strokes"] = 0
            self._reset_records()
            self._timer_save()
            win.destroy()

        gap = u(12)
        bw = (W - PAD * 2 - gap) / 2
        b1 = (PAD, y, PAD + bw, y + u(42))
        b2 = (PAD + bw + gap, y, W - PAD, y + u(42))
        rr(*b1, u(16), fill="#f4f1f5", outline="")
        cv.create_text((b1[0] + b1[2]) / 2, y + u(21), text="새로 시작",
                       font=self._uf(10, True), fill=cd["sub"])
        rr(*b2, u(16), fill=cd["fill"], outline="")
        cv.create_text((b2[0] + b2[2]) / 2, y + u(21), text="닫기",
                       font=self._uf(10, True), fill="#ffffff")

        def on_click(e):
            if b1[0] <= e.x <= b1[2] and b1[1] <= e.y <= b1[3]:
                reset_and_close()
            elif b2[0] <= e.x <= b2[2] and b2[1] <= e.y <= b2[3]:
                win.destroy()
        cv.bind("<Button-1>", on_click)
        win.update_idletasks()
        sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
        px = min(max(self.root.winfo_rootx() - 40, 10), max(sw - W - 10, 10))
        py = min(max(self.root.winfo_rooty() - 20, 10), max(sh - H - 60, 10))
        win.geometry(f"+{int(px)}+{int(py)}")

    def _update_pages(self):
        """보여 줄 안내 묶음들 — 오래된 것부터. 기록이 없으면 방금 것만."""
        pages = []
        try:
            with open(os.path.join(self.state_dir, UPDATE_LOG),
                      encoding="utf-8") as fp:
                got = json.load(fp)
            if isinstance(got, list):
                pages = [g for g in got if g.get("notes")]
        except Exception:
            pass
        if not pages and self._update_notes:
            pages = [{"ver": 0, "notes": list(self._update_notes)}]
        return pages

    def _show_update_popup(self):
        """무엇이 바뀌었는지 알려 주는 창.

        지난 안내도 화살표로 넘겨 볼 수 있다. 못 보고 지나간 사이에 다음
        업데이트가 오면 예전 것이 덮여 사라지던 문제 때문이다.
        """
        pages = self._update_pages()
        self._update_notes = []
        if not pages or self._update_win is not None:
            return
        cd, u = self.card, self._ui
        W, PAD = u(330), u(20)
        head_h = u(78)
        page = [len(pages) - 1]          # 처음에는 가장 최근 것

        win = tk.Toplevel(self.root)
        self._update_win = win
        win.title("업데이트")
        win.attributes("-topmost", True)
        win.resizable(False, False)
        win.configure(bg=cd["panel"])
        top = tk.Frame(win, bg=cd["panel"])
        top.pack()
        cv = tk.Canvas(top, width=W, bg=cd["panel"], highlightthickness=0)
        cv.pack(side="left")
        sb = tk.Scrollbar(top, orient="vertical", command=cv.yview)
        cv.config(yscrollcommand=sb.set)
        bar = tk.Canvas(win, bg=cd["panel"], highlightthickness=0)
        bar.pack()
        hits = []

        def rr(c, x0, y0, x1, y1, r, **kw):
            pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r,
                   x1, y1, x1 - r, y1, x0 + r, y1, x0, y1, x0, y1 - r,
                   x0, y0 + r, x0, y0]
            return c.create_polygon(pts, smooth=True, **kw)

        def wrap(font, notes):
            inner = W - PAD * 2 - u(46)
            out = []
            for note in notes:
                cur, head = "", True
                for word in str(note).split():
                    t = (cur + " " + word).strip()
                    tid = cv.create_text(-4000, -4000, text=t, font=font,
                                         anchor="w")
                    x0, _, x1, _ = cv.bbox(tid)
                    cv.delete(tid)
                    if cur and x1 - x0 > inner:
                        out.append((cur, head))
                        cur, head = word, False
                    else:
                        cur = t
                if cur:
                    out.append((cur, head))
            return out

        def close(_e=None):
            self._update_win = None
            win.destroy()

        def flip(d):
            page[0] += d
            render()

        def render():
            cv.delete("all")
            bar.delete("all")
            hits.clear()
            i = max(0, min(page[0], len(pages) - 1))
            page[0] = i
            font = self._uf(9)
            lines = wrap(font, pages[i].get("notes") or [])
            row_h = u(22)
            body_h = u(14) + row_h * len(lines) + u(14)
            content_h = u(20) + head_h + u(16) + body_h + u(20)
            btn_h = u(40) + u(40)
            view_h = min(content_h,
                         max(u(160),
                             self.root.winfo_screenheight() - btn_h - u(90)))
            scrolling = content_h > view_h
            cv.config(height=view_h, scrollregion=(0, 0, W, content_h))
            if scrolling:
                sb.pack(side="right", fill="y")
            else:
                sb.pack_forget()
            win.update_idletasks()
            total_w = W + (max(sb.winfo_reqwidth(), u(14)) if scrolling else 0)
            bar.config(width=total_w, height=btn_h)

            y = u(20)
            rr(cv, PAD, y, W - PAD, y + head_h, u(16), fill=cd["soft"],
               outline=cd["border"], width=2)
            cv.create_text(W / 2, y + u(24), text="새 버전으로 업데이트 됐어요",
                           font=self._uf(11, True), fill=cd["text"])
            try:
                v = int(pages[i].get("ver") or 0)
                when = time.strftime("%Y-%m-%d", time.localtime(v)) if v else ""
            except Exception:
                when = ""
            sub = when or "이번에 바뀐 점이에요"
            if len(pages) > 1:
                sub += "   (%d / %d)" % (i + 1, len(pages))
            cv.create_text(W / 2, y + u(46), text=sub,
                           font=self._uf(9), fill=cd["sub"])
            if len(pages) > 1:               # 지난 안내로 넘기는 화살표
                for sign, cx in ((-1, PAD + u(20)), (1, W - PAD - u(20))):
                    on = (i > 0) if sign < 0 else (i < len(pages) - 1)
                    col = cd["fill"] if on else cd["line"]
                    cy = y + head_h / 2
                    for dy in (-u(5), u(5)):
                        cv.create_line(cx - sign * u(3), cy + dy,
                                       cx + sign * u(3), cy, width=2,
                                       capstyle="round", fill=col)
                    if on:
                        hits.append((cx - u(14), cy - u(14), cx + u(14),
                                     cy + u(14), (lambda d: lambda: flip(d))(sign)))
            y += head_h + u(16)
            rr(cv, PAD, y, W - PAD, y + body_h, u(14), fill="#ffffff",
               outline=cd["line"], width=1)
            ly = y + u(14) + u(11)
            for text, is_first in lines:
                if is_first:
                    cv.create_oval(PAD + u(16), ly - u(3),
                                   PAD + u(22), ly + u(3),
                                   fill=cd["fill"], outline="")
                cv.create_text(PAD + u(32), ly, anchor="w", text=text,
                               font=font, fill=cd["text"])
                ly += row_h
            cv.yview_moveto(0)

            by = u(20)
            b = (PAD, by, total_w - PAD, by + u(40))
            rr(bar, b[0], b[1], b[2], b[3], u(14), fill=cd["fill"], outline="")
            bar.create_text(total_w / 2, by + u(20), text="확인",
                            font=self._uf(10, True), fill="#ffffff")
            bar.bind("<Button-1>", lambda e: close()
                     if b[0] <= e.x <= b[2] and b[1] <= e.y <= b[3] else None)
            if scrolling:
                def on_wheel(e):
                    cv.yview_scroll(-1 if e.delta > 0 else 1, "units")
                for wgt in (win, cv, bar):
                    wgt.bind("<MouseWheel>", on_wheel)
            else:
                for wgt in (win, cv, bar):
                    wgt.unbind("<MouseWheel>")

        def on_click(e):
            cy = cv.canvasy(e.y)             # 스크롤된 만큼 좌표를 맞춘다
            for x0, y0, x1, y1, fn in list(hits):
                if x0 <= e.x <= x1 and y0 <= cy <= y1:
                    fn()
                    return

        cv.bind("<Button-1>", on_click)
        win.protocol("WM_DELETE_WINDOW", close)
        render()
        win.update_idletasks()
        sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
        px = min(max(self.root.winfo_rootx() - 40, 10),
                 max(sw - win.winfo_width() - 10, 10))
        py = min(max(self.root.winfo_rooty() - 20, 10),
                 max(sh - win.winfo_height() - 60, 10))
        win.geometry("+%d+%d" % (int(px), int(py)))

    def _uf(self, size, bold=False):
        """별도 창(환경설정·브리핑·메뉴)용 글꼴 — 화면 배율을 그대로 따른다.

        이 창들은 그림 위가 아니라 보통 창이라, 다른 프로그램처럼 배율을
        반영해야 어느 컴퓨터에서든 적당한 크기로 보인다.
        """
        n = max(7, round(size * getattr(self, "ui_k", 1.0)))
        return ("Malgun Gothic", n, "bold") if bold else ("Malgun Gothic", n)

    def _ui(self, px):
        """별도 창의 치수(px)도 같은 배율로."""
        return round(px * getattr(self, "ui_k", 1.0))

    def _cf(self, size, bold=False):
        """글자 크기 설정을 반영한 글꼴."""
        n = max(6, round(size * getattr(self, "font_k", 1.0)))
        return ("Malgun Gothic", n, "bold") if bold else ("Malgun Gothic", n)

    TW_CACHE_MAX = 400           # 글자 폭 캐시 상한

    def _mw(self, text, font):
        """그 글꼴로 글자를 그리면 폭이 얼마인지 (측정값 캐시)."""
        key = (text, font)
        w = self._tw_cache.get(key)
        if w is None:
            # 카드의 시간 글자는 1초마다 달라져서 열쇠가 끝없이 쌓인다.
            # 하루 켜 두면 9만 개(25MB)까지 갔다 — 다른 캐시처럼 상한을 둔다.
            # 다시 재는 값이라 비워도 그림은 그대로다.
            if len(self._tw_cache) > self.TW_CACHE_MAX:
                self._tw_cache.clear()
            t = self.canvas.create_text(-3000, -3000, text=text, anchor="nw",
                                        font=font)
            bb = self.canvas.bbox(t)
            w = (bb[2] - bb[0]) if bb else len(text) * 11
            self.canvas.delete(t)
            self._tw_cache[key] = w
        return w

    def _mh(self, font):
        """그 글꼴의 글자 높이(px)."""
        key = ("__height__", font)
        h = self._tw_cache.get(key)
        if h is None:
            t = self.canvas.create_text(-3000, -3000, text="가", anchor="nw",
                                        font=font)
            bb = self.canvas.bbox(t)
            h = (bb[3] - bb[1]) if bb else 16
            self.canvas.delete(t)
            self._tw_cache[key] = h
        return h

    def _fit(self, text, size, max_w, bold=False):
        """카드 안에 들어가는 가장 큰 글꼴.

        카드 크기는 고정이라, 글자 크기를 키우면 상태와 시간이 서로 파고든다.
        그래서 정해진 폭을 넘으면 들어갈 때까지 한 단계씩 줄인다. 설정한
        크기가 카드에 안 맞아도 겹치지는 않게 하는 안전장치다.
        """
        n = max(6, round(size * getattr(self, "font_k", 1.0)))
        while n > 6:
            f = self._cf_n(n, bold)
            if self._mw(text, f) <= max_w:
                return f
            n -= 1
        return self._cf_n(6, bold)

    @staticmethod
    def _cf_n(n, bold=False):
        return ("Malgun Gothic", n, "bold") if bold else ("Malgun Gothic", n)

    def _draw_timer(self, state, sleeping, now):
        c = self.canvas
        cd = self.card
        active = state == "work"
        dot, status = self._status_of(state, sleeping)
        t = int(self._shown_secs())
        label = f"{t // 3600}:{t % 3600 // 60:02d}:{t % 60:02d}"
        g = self._card_geom()
        x0, y0, x1, y1 = g["x0"], g["y0"], g["x1"], g["y1"]
        pad = 14

        self._draw_deco(x0, y0, x1, y1)
        self._rrect(x0 + 2, y0 + 3, x1 + 2, y1 + 3, 16, fill="#e3e6ee", outline="")
        self._rrect(x0, y0, x1, y1, 16, fill=cd["bg"], outline=cd["border"], width=2)

        def status_dot(px, py):
            pulse = 1.5 + math.sin(now * 4) * 1.5 if active else 0
            r = 5 + pulse * 0.5
            c.create_oval(px - r, py - r, px + r, py + r, fill=dot, outline="")

        if self.has_clock and self.clock_open:
            # 세로 카드: 상태(위) → 시계(가운데) → 시간(아래) — 모두 정중앙 정렬
            cxm = (x0 + x1) / 2
            f_stat = self._fit(status, 8, (x1 - x0) - 34)
            tw = self._mw(status, f_stat)
            gx = cxm - (16 + tw) / 2            # 점+간격+텍스트 그룹 중앙
            status_dot(gx + 5, y0 + 16)
            c.create_text(gx + 16, y0 + 16, anchor="w", text=status,
                          font=f_stat, fill=cd["sub"])
            R = 38
            clock_cy = y0 + 30 + R
            self._draw_clock(cxm, clock_cy, R, now)
            c.create_text(cxm, clock_cy + R + 18, text=label,
                          font=self._fit(label, 14, (x1 - x0) - 20, True),
                          fill=cd["text"])
        elif self.has_clock:
            # 접힘: 상태 + 시간 한 줄 (게이지 없음)
            row = y0 + 20
            status_dot(x0 + pad + 5, row)
            avail = (x1 - pad) - (x0 + pad + 16)
            f_time = self._fit(label, 13, avail * 0.62, True)
            f_stat = self._fit(status, 8,
                               avail - self._mw(label, f_time) - 8)
            c.create_text(x0 + pad + 16, row, anchor="w", text=status,
                          font=f_stat, fill=cd["sub"])
            c.create_text(x1 - pad, row, anchor="e", text=label,
                          font=f_time, fill=cd["text"])
        else:
            # 게이지형(준사): 상태+시간 윗줄 + 목표 진행바 아랫줄
            row1 = y0 + 20
            status_dot(x0 + pad + 5, row1)
            # 마감은 카드가 아니라 말풍선 목록으로 보여 준다. 카드에 딱지를
            # 넣었더니 그 폭만큼 상태·시간 글자가 줄어 읽기 힘들어졌다.
            avail = (x1 - pad) - (x0 + pad + 16)
            f_time = self._fit(label, 13, avail * 0.62, True)
            f_stat = self._fit(status, 8,
                               avail - self._mw(label, f_time) - 8)
            c.create_text(x0 + pad + 16, row1, anchor="w", text=status,
                          font=f_stat, fill=cd["sub"])
            c.create_text(x1 - pad, row1, anchor="e", text=label,
                          font=f_time, fill=cd["text"])
            goal = max(float(self.us["goal_hours"]), 0.5) * 3600
            frac = min(self._shown_secs() / goal, 1.0)
            row2 = y0 + 45
            bx0, bx1 = x0 + pad + 2, x1 - pad - 36
            c.create_line(bx0, row2, bx1, row2, width=6, capstyle="round",
                          fill=cd["track"])
            if frac > 0.01:
                c.create_line(bx0, row2, bx0 + (bx1 - bx0) * frac, row2,
                              width=6, capstyle="round",
                              fill="#7ccf8f" if frac >= 1.0 else cd["fill"])
            c.create_text(x1 - pad, row2, anchor="e", text=f"{int(frac * 100)}%",
                          font=self._fit(f"{int(frac * 100)}%", 7, 34, True),
                          fill="#5aa86e" if frac >= 1.0 else cd["sub"])
            if self.fun:                      # 작업 종료 버튼
                bw = 104
                bx = (x0 + x1) / 2
                by = y1 - 22
                r = (bx - bw / 2, by - 11, bx + bw / 2, by + 11)
                self._rrect(*r, 11, fill=cd["fill"], outline="")
                c.create_text(bx, by, text="작업 종료",
                              font=self._fit("작업 종료", 8, bw - 12, True), fill="#ffffff")
                self._end_btn = r

    # ── 매 프레임 갱신 (~30fps) ──────────────────────────────────────────
    def _log_error(self, where):
        """한 프레임이 터져도 프로그램은 계속 돌게 — 원인은 파일로 남긴다."""
        self._err_count = getattr(self, "_err_count", 0) + 1
        if self._err_count > 20:
            return
        try:
            import traceback
            with open(os.path.join(self.state_dir, ".error.log"), "a",
                      encoding="utf-8") as fp:
                fp.write(f"\n===== {time.strftime('%Y-%m-%d %H:%M:%S')} {where}\n")
                fp.write(f"char={self.char} frozen={getattr(sys, 'frozen', False)} "
                         f"scale={self.s:.3f} oy={self.oy} WH={self.W}x{self.H}\n")
                fp.write(f"timer_on={self.timer_on} fun={self.fun} "
                         f"pets={list(getattr(self, '_pet_hide', {}))} "
                         f"has={sorted(k for k, v in self.has.items() if v)}\n")
                fp.write(f"settings={self.us}\n")
                traceback.print_exc(file=fp)
        except Exception:
            pass

    def _put(self, name, x, y, anchor="nw"):
        """파츠 이미지 그리기. 파일이 없으면 조용히 건너뛴다(업데이트 끊김 대비)."""
        im = self.im.get(name)
        if im is None:
            return False
        self.canvas.create_image(x, y, image=im, anchor=anchor)
        return True

    FAIL_FORGET = 300            # 이 시간(초) 넘게 안 터졌으면 실패 횟수를 잊는다

    def _safe(self, where, fn, *args):
        """부분 실패가 화면 전체를 지우지 못하게 — 3번 터지면 그 구역만 끈다.

        다만 영영 꺼지면 안 된다. 아침에 잠깐 터진 것 때문에 저녁까지 팔이
        안 나오는 식이 되기 때문이다. 마지막 실패가 한참 전이면 다시 센다.
        """
        n = self._fail.get(where, 0)
        if n and time.time() - self._fail_at.get(where, 0) > self.FAIL_FORGET:
            n = 0
            self._fail[where] = 0
        if n >= 3:
            return
        try:
            fn(*args)
        except Exception:
            self._fail[where] = n + 1
            self._fail_at[where] = time.time()
            self._log_error(where)

    def tick(self):
        # 다음 프레임을 먼저 예약한다 — 중간에 예외가 나도 루프가 죽지 않게.
        # 입력이 없으면 볼 것도 없으므로 프레임을 낮춰 CPU를 아낀다.
        # (자는 중 10fps / 5초 이상 무입력 15fps / 작업 중 30fps)
        quiet = time.time() - max(self.last_key, self.last_pointer)
        self._tick_after = self.root.after(
            100 if self._sleeping else (66 if quiet > 5.0 else 33), self.tick)
        try:
            self._tick_body()
        except Exception:
            self._log_error("tick")
            try:
                self.draw(time.time())      # 지워진 화면을 다시 채운다
            except Exception:
                self._log_error("redraw")

    def _tick_body(self):
        now = time.time()
        if self._macin is not None:
            self._safe("mac_input", self._poll_mac_input)
        if self.key_events != self._seen_keys:
            self._seen_keys = self.key_events
            self.last_key = now
            self.squash_until = now + 0.10
            pen_typing = now - self.last_pointer > 2.0
            self.tap_side = (not self.tap_side) if pen_typing else False
            if pen_typing and self.tap_side:
                self.pen_ang_t = random.uniform(*PEN_KB_ROT)
                self.pen_down_until = now + 0.09
            else:
                self.key_ang_t = random.uniform(*KEY_ROT)
                self.left_down_until = now + 0.09
        if now >= self.next_blink:
            self.blink_until = now + 0.12
            self.next_blink = now + random.uniform(2.5, 5.5)
        # 그림자: 본체를 따라오고, 주기적으로 z순서(본체 바로 아래) 재고정
        # 창이 실제로 움직였을 때만 따라 옮긴다. 위치가 그대로인데도 주기적으로
        # z순서를 다시 밀어넣으면 그림자가 눈에 띄게 깜빡인다.
        if (self.shadow is not None or self.todo_panel is not None
                or self.due_panel is not None):
            pos = (self.root.winfo_rootx(), self.root.winfo_rooty())
            if pos != self._last_pos:
                self._last_pos = pos
                self._z_check = now
                if self.shadow is not None:
                    self.shadow.place(*pos, self._main_hwnd)
                if self.todo_panel is not None:
                    self.todo_panel.place(*pos)
            # 캐릭터를 누르면 그 창이 맨 앞으로 올라와 말풍선을 덮는다.
            # 놓친 경우를 위해 짧은 주기로도 다시 올려 둔다.
            if now - self._panel_z > 0.5:
                self._panel_z = now
                for _p in (self.todo_panel, self.due_panel):
                    if _p is not None:
                        _p.raise_above()
            if self.due_panel is not None:
                self._safe("due", self._due_tick)
            elif self.shadow is not None and now - self._z_check > 8.0:
                self._z_check = now          # z순서만 가끔 재고정
                self.shadow.place(*pos, self._main_hwnd)
        # 기존 타이머(에이전트)에게 '캐릭터 타이머가 살아 있다'고 알린다.
        # 이게 없으면 에이전트가 자기 자식 프로세스만 보고 판단해, 따로 띄운
        # 캐릭터가 있어도 창을 다시 띄워 둘이 같이 보인다.
        if self.ws_path is not None and now - self._beat_t > 2.0:
            self._beat_t = now
            try:
                base = os.path.dirname(self.ws_path)
                with open(os.path.join(base, ".mascot_live"), "w") as fp:
                    fp.write(str(now))
                # PID는 따로 남긴다. 살아있음 신호에 같이 적으면 옛 타이머가
                # 그 파일을 숫자로 못 읽어 '캐릭터가 죽었다'고 보고 스스로
                # 종료해 버린다.
                if not self._pid_written:
                    self._pid_written = True
                    with open(os.path.join(base, ".mascot_pid"), "w") as fp:
                        fp.write(str(os.getpid()))
            except Exception:
                pass

        # 끝난 타자 소리 장치 정리
        if self.sndpack is not None and now - getattr(self, "_snd_reap", 0) > 2.0:
            self._snd_reap = now
            try:
                self.sndpack.reap()
            except Exception:
                pass
        self.draw(now)

    def _quad_xy(self, u, v):
        (tlx, tly), (trx, try_), (brx, bry), (blx, bly) = self.quad
        top = (tlx + (trx - tlx) * u, tly + (try_ - tly) * u)
        bot = (blx + (brx - blx) * u, bly + (bry - bly) * u)
        return (top[0] + (bot[0] - top[0]) * v,
                top[1] + (bot[1] - top[1]) * v)

    def _pos(self, name):
        x, y = self.layout[name]["pos"]
        return x * self.s + self.ox, y * self.s + self.oy

    def _arm_deg(self, dx, dy, which="r"):
        """어깨→손끝 방향으로 팔이 돌아간 각도 (손도 같은 각도로 돌린다)."""
        e = self._arm_src.get(which)
        if e is None:
            return 0.0
        nx, ny = e[1]
        return math.degrees(math.atan2(dx, dy) - math.atan2(nx, ny))


    def _pen_at_tip(self, tx, ty, deg):
        """펜 쥔 손을 팔 손끝(tx, ty)에 붙여 팔과 같은 각도로 그린다."""
        e = self._pen_rot
        if e is None:
            return False
        k = round(deg)
        if k not in e["cache"]:
            if len(e["cache"]) > 90:
                e["cache"].clear()
            e["cache"][k] = ImageTk.PhotoImage(
                self._hard(e["pil"].rotate(k, resample=self._resample())))
        self.canvas.create_image(tx, ty, image=e["cache"][k], anchor="center")
        return True

    ARM_CACHE_MAX = 500          # 늘인 팔 그림 캐시 상한 (한 장이 꽤 크다)

    def _stretched_arm(self, dx, dy, which="r"):
        """어깨에서 손끝까지를 잇도록 늘이고 돌린 팔 그림.

        which — "r" 오른팔, "rm" 오른팔 좌우반전(안쪽으로 모을 때), "l" 왼팔.
        """
        e = self._arm_src.get(which)
        if e is None:
            return None
        src, (nx, ny), atop, _abot = e
        nat_len = max(math.hypot(nx, ny), 8.0)
        cur_len = max(math.hypot(dx, dy), 8.0)
        k = max(0.25, min(3.0, cur_len / nat_len))   # 늘이기 배율 상한선
        deg = math.degrees(math.atan2(dx, dy) - math.atan2(nx, ny))
        key = (round(k * 25), round(deg), which)
        hit = self._arm_cache.get(key)
        if hit is None:
            if len(self._arm_cache) > self.ARM_CACHE_MAX:
                # 통째로 비우면 다음 프레임부터 다시 수백 장을 만드느라
                # 메모리가 계단처럼 뛴다(실측 200MB까지). 오래된 절반만
                # 버리면 자주 쓰는 각도는 남아서 다시 만드는 양이 적다.
                for _old in list(self._arm_cache)[:self.ARM_CACHE_MAX // 2]:
                    del self._arm_cache[_old]
            w, h = src.size
            nh = max(8, round(h * k))
            im = src.resize((w, nh), Image.LANCZOS)
            im = im.rotate(deg, expand=True, resample=self._resample())
            # 돌린 그림 안에서 '어깨 접합점'이 어디로 갔는지 따라간다. 이걸
            # 안 하고 가운데에 맞춰 그리면 팔을 늘일수록 어깨가 몸에서 떨어져
            # 그 사이로 머리카락과 배경이 비친다.
            a = math.radians(deg)
            ox_ = atop[0] - w / 2.0
            oy_ = atop[1] * k - nh / 2.0
            rx = ox_ * math.cos(a) + oy_ * math.sin(a) + im.width / 2.0
            ry = -ox_ * math.sin(a) + oy_ * math.cos(a) + im.height / 2.0
            hit = (ImageTk.PhotoImage(self._hard(im)), (rx, ry))
            self._arm_cache[key] = hit
        return hit

    def draw(self, now):
        c = self.canvas
        c.delete("all")
        f = self._force

        idle = idle_seconds()
        sleeping = idle > max(float(self.us["sleep_min"]), 1) * 60 or f.get("sleep", False)
        self._sleeping = sleeping        # tick의 프레임 간격 조절용

        if sleeping:
            breathe = math.sin(now * 1.1) * 2.5     # 자는 동안은 느리고 깊게
        else:
            breathe = math.sin(now * 2.0) * 1.5
        # 몸짓 값은 여기서 먼저 지운다. _gest_tick 안에서만 지우면, 그 구역이
        # 세 번 터져 꺼졌을 때 마지막 자세가 그대로 남아 캐릭터가 굳는다.
        self._g_dy = self._g_hdy = self._g_tilt = 0.0
        self._g_hands = None
        self._g_eyes_shut = self._g_smile = False
        if self._tray_q:
            self._safe("tray_tick", self._tray_tick)
        self._safe("stretch", self._stretch_tick, now, sleeping)
        self._safe("gesture", self._gest_tick, now, sleeping)
        self._safe("goal", self._goal_tick, now)
        squash = 3 if now < self.squash_until else 0
        yo = breathe + squash + self._g_dy
        if self.fun and now < self.click_bounce:      # 클릭 반응: 콩 하고 튐
            t = (self.click_bounce - now) / 0.45
            yo -= math.sin(t * math.pi) * 7

        cx, cy = cursor_pos()
        wx = self.root.winfo_rootx() + self.W // 2
        wy = self.root.winfo_rooty() + self.H // 2
        pdx = max(-5, min(5, (cx - wx) / 60))
        pdy = max(-3, min(4, (cy - wy) / 90))
        # 몸짓 중에는 눈동자를 가운데로 모은다. 고개를 기울이면 미리 합쳐 둔
        # 머리(눈동자가 가운데에 구워져 있다)로 그려지는데, 기울기가 0 근처를
        # 오갈 때마다 두 방식이 번갈아 쓰여 눈동자가 대각선으로 튄다.
        if self.gest is not None:
            pdx = pdy = 0.0

        pen_typing = (now - self.last_pointer > 2.0) and (now - self.last_key < 1.8)
        if "pen" in f or f.get("type"):
            pen_typing = bool(f.get("type"))
        # 타자 칠 때는 깃펜이 사라지므로 그 자리의 그림자도 같이 없앤다.
        # 다만 pen_typing은 마우스가 조금만 움직여도 뒤집히므로, 상태가
        # 잠시 유지된 뒤에만 교체한다 (매번 바꾸면 그림자가 깜빡인다).
        if pen_typing != self._shadow_want:
            self._shadow_want = pen_typing
            self._shadow_since = now
        elif (self.shadow is not None and self.shadow_img_type is not None
                and pen_typing != self._shadow_typing
                and now - self._shadow_since > 0.5
                and now - self._shadow_swap > 0.7):
            self._shadow_typing = pen_typing
            self._shadow_swap = now
            self._shadow_base = self.shadow_img_type if pen_typing else self.shadow_img
            if not self._pet_sh_on:
                self.shadow.set_image(self._shadow_base)

        blinking = (sleeping or now < self.blink_until or self._g_eyes_shut
                    or f.get("blink", False)) \
            and (self.blink_cfg is not None or self.has.get("eyes_closed"))
        smiling = bool(self.has.get("smile")
                       and (now < self.smile_until or self._g_smile
                            or self._stretch_hover
                            or f.get("smile", False)))
        if smiling:
            blinking = False

        self._pet_drawn = []
        try:
            state = self._timer_tick(now, idle) if self.timer_on else "idle"
        except Exception:
            state, _ = "idle", self._log_error("timer_tick")
        # 아래는 모두 구역 격리 — 하나가 터져도 캐릭터 본체는 그려진다
        self._safe("greet", self._greet_tick, now, state)
        self._safe("fun_tick", self._fun_tick, now, state, sleeping)
        if self.timer_on:
            self._safe("timer", self._draw_timer, state, sleeping, now)

        # ── 몸 (+머리 없는 캐릭터는 여기서 얼굴까지) ─────────────────────
        # 개는 머리를 팔 위에 그려야 어깨가 안 튀어나오므로, 얼굴을 팔 뒤로 미룬다.
        head_early = bool(self.cfg.get("arms_over_head") and self.has.get("head"))
        # 몸 뒤 파츠(사가 양갈래·기뽀 날개) — 몸보다 먼저, 살아 있게 움직인다.
        # 소품의 뒤쪽 조각(악마 꼬리·천사 날개)이 있으면 그것이 자리를 대신한다.
        if self.has.get("prop_back"):
            self._safe("prop_back", self._draw_prop_back, now, yo)
        elif self.has.get("back"):
            self._safe("back", self._draw_back, now, yo)
        bx, by = self._pos("body_open")
        self._safe("body", self._put, "body_open", bx, by + yo)
        if not self.has.get("head"):
            self._safe("face", self._draw_face, yo, pdx, pdy, blinking, smiling)
        elif head_early:                # 준사: 책상·팔이 머리 위 (PSD 순서)
            self._safe("head", self._draw_head, now, yo, pdx, pdy,
                       blinking, smiling, sleeping)

        # 반려동물은 책상 바로 앞(=책상에 가려지게) 그린다
        if not self.cfg.get("pet_front"):
            self._safe("pet", self._draw_pet, now)

        # ── 책상 (+옵션: 화면 낙서) ──────────────────────────────────────
        dx_, dy_ = self._pos("desk")
        self._safe("desk", self._put, "desk", dx_, dy_)
        if self.us.get("trail"):
            if self.strokes and now - self.last_drag > 12:
                self.strokes = []
            for st in self.strokes:
                if len(st) >= 2:
                    c.create_line(*[v for p in st for v in p],
                                  fill=self.cfg.get("trail_color", "#8fd0ff"),
                                  width=2, smooth=True)
                elif st:
                    px, py = st[0]
                    c.create_oval(px - 1, py - 1, px + 1, py + 1,
                                  fill=self.cfg.get("trail_color", "#8fd0ff"),
                                  outline="")
        else:
            self.strokes = []

        # 앞으로 나오는 반려동물: 얼굴 위 · 팔 아래 (책상선 마스크는 그대로)
        if self.cfg.get("pet_front"):
            self._safe("pet", self._draw_pet, now)

        self._safe("arms", self._draw_arms, now, f, yo, pen_typing, cx, cy)

        if self.has.get("scarf"):       # 목도리 — 팔 위, 머리 아래
            sx, sy = self._pos("scarf")
            self._safe("scarf", self._put, "scarf", sx, sy + yo)

        # ── 머리(팔 위) + 얼굴 — 개처럼 머리를 분리한 캐릭터 ──────────────
        # 머리를 팔보다 위에 그려 어깨가 머리 밖으로 튀어나오지 않게 한다.
        if self.has.get("head") and not head_early:
            self._safe("head", self._draw_head, now, yo, pdx, pdy,
                       blinking, smiling, sleeping)
        if self.cfg.get("pen_over_head"):     # 퀸시: 깃펜이 맨 위 레이어
            self._safe("pen_hand", self._draw_pen_hand)
        if self._g_hands is not None:        # 제스처 손 — 머리보다 위
            self._safe("gesture_arms", self._draw_gesture_arms, yo)

        # 수면 모드: 머리 위쪽에 둥실거리는 zzZ (머리보다 위에 그린다)
        if sleeping:
            hx0, hy0, hx1, hy1 = self._head_box
            zx = min(hx1 - 14, self.W - 42)
            zy = hy0 + self.oy + yo + 10
            for i, (dx, dy, size, color) in enumerate((
                    (0, 22, 10, "#aab7cc"),
                    (13, 4, 13, "#93a4c2"),
                    (28, -16, 16, "#7c90b5"))):
                bob = math.sin(now * 1.6 + i * 0.9) * 3
                c.create_text(zx + dx, zy + dy + bob, text="z" if i == 0 else "Z",
                              font=("Malgun Gothic", size, "bold"), fill=color)

        if self.notes:                  # 음표는 머리보다 위로 떠오른다
            self._safe("notes", self._draw_notes)

        # ── 귀여운 연출: 고깔모자 → 폭죽 → 말풍선 (맨 위) ────────────────
        if self.fun:
            self._safe("hat", self._draw_hat, yo)
        if self.stretch_pending:
            self._safe("tap_ring", self._draw_tap_ring, now)
        if self.can_talk:
            self._safe("particles", self._draw_particles)
            self._safe("bubble", self._draw_bubble, yo)
        self._safe("pet_shadow", self._update_pet_shadow)

    AUTO_MON = "자동 (커서가 있는 화면)"

    def monitor_names(self):
        """환경설정에 보여 줄 화면 목록. 열 때마다 다시 잰다(연결이 바뀌므로)."""
        out = [self.AUTO_MON]
        for i, r in enumerate(list_monitors(), 1):
            out.append(f"{i}번 화면 {r[2] - r[0]}x{r[3] - r[1]}")
        return out

    def _pen_mon_rect(self):
        """펜이 따라갈 화면. 자동이거나 그 화면이 사라졌으면 None.

        고르는 칸을 없앤 캐릭터는 저장돼 있던 값도 무시하고 늘 자동으로 둔다.
        안 그러면 예전에 골라 둔 화면에 묶인 채 되돌릴 방법이 없어진다.
        """
        if not self.cfg.get("pen_monitor_pick"):
            return None
        raw = str(self.us.get("pen_monitor", "") or "")
        if not raw or raw.startswith("자동"):
            return None
        try:
            n = int(raw.split("번")[0])
        except Exception:
            return None
        mons = list_monitors()
        return mons[n - 1] if 1 <= n <= len(mons) else None

    # 점으로 시작해야 한다 — 파츠 폴더에 생기는 파일이라, 점이 없으면
    # make_manifest가 배포 payload에 그대로 실어 보낸다.
    PEN_DIAG = ".pen_diag.txt"    # 진단 기록 파일
    PEN_DIAG_MAX = 150            # 이 줄 수까지만 남긴다

    def _pen_diag_head(self):
        """진단 기록 첫머리 — 프로그램이 본 화면 구성 그대로."""
        if self._diag_left <= 0:
            return
        try:
            lines = [
                "=== %s / %s ===" % (time.strftime("%Y-%m-%d %H:%M:%S"),
                                     self.char),
                "IS_WIN=%s IS_MAC=%s" % (IS_WIN, IS_MAC),
                "mac_monitors() = %r" % (mac_monitors(),),
                "list_monitors() = %r" % (list_monitors(),),
                "Tk 화면 = %dx%d" % (self.root.winfo_screenwidth(),
                                    self.root.winfo_screenheight()),
                "pen_monitor 설정 = %r" % (self.us.get("pen_monitor"),),
                "_pen_mon_rect() = %r" % (self._pen_mon_rect(),),
                "시작 커서 = %r" % (cursor_pos(),),
                "-- 아래는 마우스를 옮길 때마다 한 줄씩 --",
            ]
            with open(os.path.join(self.state_dir, self.PEN_DIAG), "w",
                      encoding="utf-8") as fp:
                fp.write("\n".join(lines) + "\n")
        except Exception:
            self._diag_left = 0

    def _pen_diag_row(self, cx, cy, rect, u, v):
        """커서가 어느 화면으로 잡혔고 타블렛 어디를 짚는지 한 줄 남긴다."""
        if self._diag_left <= 0:
            return
        now = time.time()
        key = tuple(rect)
        if key == self._diag_last and now - self._diag_at < 3.0:
            return                    # 같은 화면이면 3초에 한 줄만
        self._diag_last, self._diag_at = key, now
        self._diag_left -= 1
        try:
            with open(os.path.join(self.state_dir, self.PEN_DIAG), "a",
                      encoding="utf-8") as fp:
                fp.write("%s 커서=(%d,%d) 잡힌화면=%r 타블렛=(%.2f, %.2f)\n"
                         % (time.strftime("%H:%M:%S"), cx, cy, key, u, v))
        except Exception:
            self._diag_left = 0

    def _track_pen(self, now, f, cx, cy):
        """펜 끝이 따라갈 자리를 구하고 그린 획 수·낙서 선을 기록한다.

        팔을 그리는 것과 분리해 둔다 — 몸짓 중에는 팔이 딴짓을 하지만
        사용자가 실제로 긋는 획은 그대로 세어야 하기 때문이다.
        """
        if "pen" in f:
            target = self._quad_xy(*f["pen"])
            drawing = True
        else:
            # 듀얼 모니터에서 어느 화면을 따라갈지 골랐으면 그 화면 기준으로,
            # 아니면 커서가 놓인 화면 기준으로 손 위치를 잡는다.
            ml, mt, mr, mb = self._pen_mon_rect() or monitor_at(cx, cy)
            u = min(1.0, max(0.0, (cx - ml) / max(mr - ml, 1)))
            v = min(1.0, max(0.0, (cy - mt) / max(mb - mt, 1)))
            if self._diag_left > 0:
                self._pen_diag_row(cx, cy, (ml, mt, mr, mb), u, v)
            target = self._quad_xy(u, v)
            drawing = self.mouse_pressed
        self._pen_xy[0] += (target[0] - self._pen_xy[0]) * 0.55
        self._pen_xy[1] += (target[1] - self._pen_xy[1]) * 0.55
        tx, ty = self._pen_xy
        if drawing and not getattr(self, "_stroke_prev", False):
            self.stat["strokes"] = self.stat.get("strokes", 0) + 1
        self._stroke_prev = drawing
        if drawing:
            if self._new_stroke or not self.strokes:
                self.strokes.append([])
                self._new_stroke = False
            self.strokes[-1].append((tx, ty))
            while sum(len(st) for st in self.strokes) > 300:
                self.strokes.pop(0)
        return tx, ty, drawing

    def _draw_arms(self, now, f, yo, pen_typing, cx, cy):
        """펜 추적 팔 또는 타이핑 팔 (환경 의존 코드가 많아 따로 격리)."""
        c = self.canvas
        # (펜 소리의 획 감지·속도 측정은 마우스 콜백이 맡는다 — 그리기 루프에서
        #  재면 프레임 간격만큼 늦어진다. 여기선 페이드 진행만 tick으로 돌린다.)
        # ── 오른손/오른팔: 펜 추적 또는 타이핑 파츠(어깨 축 회전) ────────
        if self.arm_pil is None or "arm_key" not in self.hop:
            return                      # 팔 파츠가 없으면 팔만 생략
        if self._g_hands is not None and self._fail.get("gesture_arms", 0) < 3:
            # 몸짓 중 — 손은 머리를 그린 뒤에 그린다. 머리가 창을 거의 다
            # 채워서, 손을 조금만 들어도 머리 뒤로 숨어 버리기 때문이다.
            # 팔은 몸짓을 하더라도 그린 획 수와 펜 소리는 계속 센다.
            self._track_pen(now, f, cx, cy)
            if self.pensnd is not None and self._pen_grain and "pen" not in f:
                self.pensnd.tick(now, enabled=True)
            return
        if pen_typing and "pen" not in f and "arm_right_typing" in self.hop:
            # 양손 타이핑: 왼손을 먼저(아래), 오른팔-타자를 나중(위) 그림
            self._draw_left(now, f)
            self.pen_ang += (self.pen_ang_t - self.pen_ang) * 0.5
            bob = 4 if now < self.pen_down_until else 0
            tx_, ty_ = self._pos("arm_right_typing")
            offx, offy = self.hop["arm_right_typing"]["off"]
            c.create_image(tx_ + offx, ty_ + offy + bob,
                           image=self._rotated_hop("arm_right_typing", self.pen_ang),
                           anchor="nw")
            if self._pen_grain and self.pensnd is not None:
                self.pensnd.tick(now, enabled=False)    # 타이핑 중엔 펜 소리 정지
        else:
            tx, ty, drawing = self._track_pen(now, f, cx, cy)
            px, py = self._pos("arm_pen")
            btx, bty = self.pen_base_tip
            ddx, ddy = tx - btx, ty - bty
            # 숨쉬기(yo)는 팔 '모양' 계산에서 뺀다. 넣으면 프레임마다 각도·길이가
            # 미세하게 달라져 팔 이미지를 끝없이 새로 만들게 된다(메모리 증가).
            # 어깨가 1~2px 오르내리는 것은 그린 위치만 옮겨 표현한다.
            sx, sy = self.arm_top
            hx_, hy_ = self.arm_bottom[0] + ddx, self.arm_bottom[1] + ddy
            arm = self._stretched_arm(hx_ - sx, hy_ - sy)
            if arm is not None:
                c.create_image(sx - arm[1][0], sy - arm[1][1] + yo * 0.25,
                               image=arm[0], anchor="nw")
            self._pen_draw = (px + ddx, py + ddy)
            if not self.cfg.get("pen_over_head"):
                self._draw_pen_hand()
            self._draw_left(now, f)
            # 연필 사각거림
            if self.pensnd is not None and "pen" not in f:
                if self._pen_grain:
                    # 획 감지·짧은 클립은 마우스 콜백에서 이미 즉시 처리됐다.
                    # 여기서는 페이드 진행과 긴 획의 루프 전환만 맡는다.
                    self.pensnd.tick(now, enabled="pen" not in f)
                elif drawing:                     # 원샷: 스트로크마다 클립 한 번
                    self._pen_release_t = None
                    if not self._pen_playing:
                        self.pensnd.play()
                        self._pen_playing = True
                elif self._pen_playing:
                    # 펜압 흔들림으로 잠깐 떨어지는 것은 무시(70ms 유예)
                    if self._pen_release_t is None:
                        self._pen_release_t = now
                    elif now - self._pen_release_t > 0.07:
                        self._pen_playing = False


    def _draw_pen_hand(self):
        """펜 쥔 손. 퀸시처럼 펜이 맨 위 레이어인 캐릭터는 머리를 그린 뒤 호출.

        늘어나는 오른팔은 목도리 아래로 들어가야 하므로 여기서 그리지 않는다.
        """
        d = self._pen_draw
        if not d:
            return
        px, py = d
        self._put("arm_pen", px, py)
        self._pen_draw = None

    HEAD_DIAG = ".head_diag.txt"     # 머리 자리 진단 기록
    HEAD_DIAG_MAX = 120

    def _head_diag(self, kind, got, want, extra=""):
        """머리가 제자리에서 벗어난 프레임을 남긴다.

        '머리가 몸에서 빠진다'는 제보를 내 컴퓨터에서 재현하지 못해, 실제로
        쓰는 컴퓨터에서 어떤 값이 나오는지 받아 보려고 둔다.
        """
        if self._hd_left <= 0:
            return
        try:
            path = os.path.join(self.state_dir, self.HEAD_DIAG)
            if not self._hd_head:
                self._hd_head = True
                with open(path, "w", encoding="utf-8") as fp:
                    fp.write("=== %s / %s ===\n" % (
                        time.strftime("%Y-%m-%d %H:%M:%S"), self.char))
                    fp.write("배율=%.3f 크기설정=%s 창=%dx%d oy=%s ox=%s\n" % (
                        self.s, self.us.get("scale_pct"), self.W, self.H,
                        self.oy, self.ox))
                    fp.write("기울기상한=%s 목=%s 머리상자=%s pad=%d\n" % (
                        self._tilt_max, self._neck, self._head_box,
                        self.TILT_PAD))
                    fp.write("-- 아래는 머리가 제자리를 벗어난 프레임 --\n")
            now = time.time()
            if now - self._hd_at < 0.25:      # 너무 촘촘히 남기지 않는다
                return
            self._hd_at = now
            self._hd_left -= 1
            with open(path, "a", encoding="utf-8") as fp:
                fp.write("%s %-6s 그린자리=%s 기대=%s %s\n" % (
                    time.strftime("%H:%M:%S"), kind, got, want, extra))
        except Exception:
            self._hd_left = 0

    def _draw_head(self, now, yo, pdx, pdy, blinking, smiling, sleeping):
        """머리 + 얼굴 (자는 중이면 목을 축으로 기울인 합성본)."""
        c = self.canvas
        hyo = yo + self._g_hdy          # 끄덕임은 머리만 움직인다
        tilt = None
        if sleeping and self._tilt_max >= 2:       # 꾸벅 — 살짝 기울여 잔다
            m = self._tilt_max
            tilt = -(m * 0.78 + m * 0.22 * math.sin(now * 0.55))
        elif abs(self._g_tilt) >= 0.5 and self._tilt_max >= 2:
            m = self._tilt_max
            tilt = max(-m, min(m, self._g_tilt))
        if tilt is not None:
            # 기울인 머리를 못 만들면 안 기울인 머리라도 그린다. 여기서 그냥
            # 터지면 머리 구역이 꺼져 얼굴이 통째로 사라진다.
            try:
                p = self.TILT_PAD
                # 눈을 감은 채 고개를 기울이는 동작(하품·꾸벅)이 있다. 눈 뜬
                # 판으로 그리면 감으라고 해도 눈이 떠진다 — 잘 때 쓰는 판이
                # 곧 눈감은 판이라 그것을 쓴다.
                mode = ("sleep" if sleeping
                        else "shut" if blinking
                        else "smile" if (smiling and self._tilt_base_smile is not None)
                        else "awake")
                img, tdx = self._sleep_head(tilt, mode)
                # 합성판은 파츠를 ox 없이 붙여 만든다. 캐릭터가 작아 카드보다
                # 좁으면 ox만큼 오른쪽으로 밀어 놓는데, 여기서 그 값을 빼먹으면
                # 고개를 기울일 때마다 머리만 ox만큼 왼쪽으로 튄다
                # (크기 50%에서 29px — '머리가 몸에서 빠진다' 제보의 원인).
                gx, gy = tdx - p + self.ox, self.oy - p + hyo
                c.create_image(gx, gy, anchor="nw", image=img)
                if self._hd_left > 0 and (abs(gx + p) > 3 or abs(tdx) > 3):
                    self._head_diag("기울임", (round(gx), round(gy)),
                                    (-p, round(self.oy - p)),
                                    "tilt=%.2f mode=%s tdx=%d hyo=%.1f 자는중=%s"
                                    % (tilt, mode, tdx, hyo, sleeping))
                if sleeping:
                    self._draw_snot(now, hyo, tilt, tdx)
            except Exception:
                tilt = None
                self._log_error("head_tilt")
        if tilt is None:
            hx, hy = self._pos("head")
            if self._hd_left > 0:
                want = self._pos("head")
                if abs(hx - want[0]) > 3:
                    self._head_diag("보통", (round(hx), round(hy + hyo)),
                                    (round(want[0]), round(want[1])),
                                    "g_tilt=%.2f 상한=%.1f" % (self._g_tilt,
                                                              self._tilt_max))
            self._put("head", hx, hy + hyo)
            self._draw_face(hyo, pdx, pdy, blinking, smiling)

    def _draw_face(self, yo, pdx, pdy, blinking, smiling=False):
        """눈동자(시선) 또는 감은 눈/웃는 얼굴 + 눈 위 덮개들."""
        c = self.canvas
        if smiling:                       # 웃는 표정 파츠가 눈을 대신한다
            drawn = False
            for name in (self.layout.get("overlays") or []):
                if name in ("body_mask", "lashes"):
                    continue
                if name == "eyes_closed":
                    sx, sy = self._pos("smile")
                    self._put("smile", sx, sy + yo)
                    drawn = True
                    continue
                if not self.has.get(name) or name == "head":
                    continue
                ox, oy_ = self._pos(name)
                self._put(name, ox, oy_ + yo)
            if not drawn:
                sx, sy = self._pos("smile")
                self._put("smile", sx, sy + yo)
            return
        if not blinking:
            ex, ey = self._pos("pupils")
            self._put("pupils", ex + pdx, ey + yo + pdy)
        elif self.blink_cfg is not None:
            (x0, y0, x1, y1), color = self.blink_cfg
            c.create_rectangle(x0, y0 + yo, x1, y1 + yo, fill=color, outline="")
        overlays = self.layout.get("overlays") or \
            ["body_mask", "lashes", "eyes_closed", "hair"]
        for name in overlays:
            if name == "head":
                continue                # 머리는 별도 처리
            if name == "eyes_closed":
                if not (blinking and self.has.get("eyes_closed")):
                    continue
            elif not self.has.get(name):
                continue
            ox, oy_ = self._pos(name)
            self._put(name, ox, oy_ + yo)

    def _draw_left(self, now, f):
        """왼손(키보드): 어깨 축 회전으로 키를 옮겨가며 타이핑."""
        if now - self.last_key > 2.5:
            self.key_ang_t = 0.0
        self.key_ang += (self.key_ang_t - self.key_ang) * 0.5
        kx, ky = self._pos("arm_key")
        kx += self.arm_key_off[0]
        ky += self.arm_key_off[1]
        offx, offy = self.hop["arm_key"]["off"]
        down = now < self.left_down_until or f.get("type")
        self.canvas.create_image(kx + offx, ky + offy + (4 if down else 0),
                                 image=self._rotated_hop("arm_key", self.key_ang),
                                 anchor="nw")

    # ── 환경설정 창 ──────────────────────────────────────────────────────
    def open_settings(self):
        """캔버스로 직접 그린 설정 창 — 그룹 카드 · 토글 · 스테퍼 · 목록."""
        if self._settings_win is not None and self._settings_win.winfo_exists():
            self._settings_win.lift()
            return
        self._settings_open = None       # 항상 접힌 상태로 열린다
        self._fb_msg = ""
        cd = self.card
        PANEL, SOFT, LINE = cd["panel"], cd["soft"], cd["line"]
        W, PAD, ROW, IN = (self._ui(372), self._ui(20),
                           self._ui(40), self._ui(18))
        FONT = "Malgun Gothic"
        FS = lambda n: max(7, round(n * self.ui_k))   # 설정 창 글꼴
        win = tk.Toplevel(self.root)
        self._settings_win = win
        win.title(f"{self.cfg.get('name', self.char)} 설정")
        win.attributes("-topmost", True)
        win.resizable(False, False)
        win.configure(bg=PANEL)

        st = dict(self.us)
        st["show_timer"] = bool(self.timer_on)
        if st.get("sound_pack") not in self.sound_packs and self.sound_packs:
            st["sound_pack"] = self.sound_packs[0]

        # 내용이 길어지면 화면 밖으로 나가므로, 위쪽은 스크롤되는 칸으로 두고
        # 저장 버튼은 아래 띠에 따로 붙여 늘 보이게 한다.
        top = tk.Frame(win, bg=PANEL)
        top.pack()
        cv = tk.Canvas(top, width=W, height=640, bg=PANEL, highlightthickness=0)
        cv.pack(side="left")
        vbar = tk.Scrollbar(top, orient="vertical", command=cv.yview)
        cv.config(yscrollcommand=vbar.set, yscrollincrement=self._ui(6))
        bar = tk.Canvas(win, width=W, height=1, bg=PANEL, highlightthickness=0)
        bar.pack()
        apps_var = tk.StringVar(value=str(st.get("work_apps", "")))
        apps_entry = tk.Entry(win, textvariable=apps_var, font=(FONT, FS(8)),
                              relief="flat", bg="#ffffff", fg=cd["text"],
                              highlightthickness=0, borderwidth=0)
        fb_on = bool(self._fb_url())
        fb_text = None
        if fb_on:
            fb_text = tk.Text(win, font=(FONT, FS(8)), relief="flat",
                              bg="#ffffff", fg=cd["text"], wrap="word",
                              highlightthickness=0, borderwidth=0)
        hits, sliders, bar_hits = [], [], []
        RX = W - PAD - IN            # 오른쪽 컨트롤 기준선
        LX = PAD + IN                # 왼쪽 라벨 기준선

        def rrect(x0, y0, x1, y1, r, on=None, **kw):
            pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1,
                   x1 - r, y1, x0 + r, y1, x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]
            return (on or cv).create_polygon(pts, smooth=True, **kw)

        def header(y):
            """캐릭터 귀 + 이름 헤더."""
            hx0, hx1 = PAD, W - PAD
            deco = cd.get("deco")
            if deco == "scarf":                 # 퀸시: 귀 대신 목도리 띠
                rrect(hx0 + 20, y - 6, hx1 - 20, y + 22, 10,
                      fill=cd["border"], outline="")
                span = (hx1 - hx0 - 96) / 4
                for i in range(5):
                    sx = hx0 + 56 + i * span
                    cv.create_line(sx, y - 3, sx - 9, y + 20,
                                   fill="#dfe5f0", width=4)
                rrect(hx0, y + 10, hx1, y + 62, 18, fill=SOFT,
                      outline=cd["border"], width=2)
                cv.create_text(W / 2, y + 36,
                               text=f"{self.cfg.get('name', self.char)} 설정",
                               font=(FONT, FS(12), "bold"), fill=cd["text"])
                return y + 78
            ec = {"cat": "#f5bdd2", "rose": "#f5bdd2"}.get(deco, "#2b2b2b")
            for ex in (hx0 + 34, hx1 - 34):
                if deco == "cat":
                    cv.create_polygon(ex - 13, y + 18, ex + 2, y - 8, ex + 13, y + 17,
                                      fill=ec, outline=cd["border"], width=2)
                else:
                    cv.create_oval(ex - 13, y - 8, ex + 13, y + 18, fill=ec, outline="")
            rrect(hx0, y + 10, hx1, y + 62, 18, fill=SOFT,
                  outline=cd["border"], width=2)
            cv.create_text(W / 2, y + 36, text=f"{self.cfg.get('name', self.char)} 설정",
                           font=(FONT, FS(12), "bold"), fill=cd["text"])
            return y + 78

        def group(y, title, rows):
            """제목 + 흰 카드 안에 행들을 균등 배치."""
            cv.create_oval(PAD + 3, y - 4, PAD + 11, y + 4,
                           fill=cd["fill"], outline="")
            cv.create_text(PAD + 18, y, anchor="w", text=title,
                           font=(FONT, FS(9), "bold"), fill=cd["fill"])
            y += 16
            # 행을 먼저 그리고 흰 카드를 뒤로 내린다. 펼친 목록이 있으면 높이가
            # 달라지는데, 카드를 먼저 그리려면 높이를 미리 알아야 해서다.
            ry = y + 7 + ROW / 2
            extra = 0
            for fn in rows:
                e = fn(ry) or 0
                ry += ROW + e
                extra += e
            h = ROW * len(rows) + 14 + extra
            bg = rrect(PAD, y, W - PAD, y + h, 16, fill="#ffffff",
                       outline=LINE, width=1)
            cv.tag_lower(bg)
            return y + h + 20

        def label(y, text):
            cv.create_text(LX, y, anchor="w", text=text,
                           font=(FONT, FS(9)), fill=cd["text"])

        def toggle(y, text, key):
            label(y, text)
            on = bool(st.get(key))
            x1, x0 = RX, RX - 46
            rrect(x0, y - 11, x1, y + 11, 11,
                  fill=cd["fill"] if on else "#e2e0e6", outline="")
            kx = x1 - 12 if on else x0 + 12
            cv.create_oval(kx - 8.5, y - 8.5, kx + 8.5, y + 8.5,
                           fill="#ffffff", outline="")

            def flip(k=key):
                st[k] = not bool(st.get(k))
            hits.append((x0 - 6, y - 16, x1 + 6, y + 16, flip))

        def stepper(y, text, key, lo, hi, step, suffix=""):
            label(y, text)
            val = float(st.get(key, lo))
            for sign, cx in ((1, RX - 13), (-1, RX - 99)):
                cv.create_oval(cx - 13, y - 13, cx + 13, y + 13,
                               fill=SOFT, outline=cd["border"], width=1)
                cv.create_line(cx - 5, y, cx + 5, y, width=2,
                               capstyle="round", fill=cd["text"])
                if sign > 0:
                    cv.create_line(cx, y - 5, cx, y + 5, width=2,
                                   capstyle="round", fill=cd["text"])

                def bump(s=sign, k=key, lo=lo, hi=hi, stp=step):
                    v = float(st.get(k, lo)) + s * stp
                    st[k] = max(lo, min(hi, round(v, 2)))
                hits.append((cx - 15, y - 15, cx + 15, y + 15, bump))
            cv.create_text(RX - 56, y, text=f"{val:g}{suffix}",
                           font=(FONT, FS(9), "bold"), fill=cd["text"])

        def slider(y, text, key, lo, hi):
            label(y, text)
            val = float(st.get(key, lo))
            sx0, sx1 = RX - 148, RX - 46
            cv.create_line(sx0, y, sx1, y, width=6, capstyle="round", fill="#efedf1")
            frac = (val - lo) / max(hi - lo, 1)
            if frac > 0.01:
                cv.create_line(sx0, y, sx0 + (sx1 - sx0) * frac, y, width=6,
                               capstyle="round", fill=cd["fill"])
            kx = sx0 + (sx1 - sx0) * frac
            cv.create_oval(kx - 9, y - 9, kx + 9, y + 9, fill="#ffffff",
                           outline=cd["fill"], width=2)
            cv.create_text(RX, y, anchor="e", text=f"{val:g}",
                           font=(FONT, FS(9), "bold"), fill=cd["text"])
            sliders.append((sx0, sx1, y, key, lo, hi))

        def chevron(cx, y, sign):
            """sign -1이면 ‹, +1이면 › 모양."""
            for dy in (-5, 5):
                cv.create_line(cx - sign * 3, y + dy, cx + sign * 3, y,
                               width=2, capstyle="round", fill=cd["fill"])

        def picker(y, text, key, options):
            label(y, text)
            if not options:
                cv.create_text(RX, y, anchor="e", text="(없음)",
                               font=(FONT, FS(8)), fill=cd["sub"])
                return
            cur = st.get(key, options[0])
            idx = options.index(cur) if cur in options else 0
            bx0, bx1 = RX - 176, RX
            rrect(bx0, y - 14, bx1, y + 14, 14, fill=SOFT,
                  outline=cd["border"], width=1)
            name = options[idx]
            if len(name) > 16:
                name = name[:15] + "…"
            cv.create_text((bx0 + bx1) / 2, y, text=name,
                           font=(FONT, FS(8)), fill=cd["text"])
            for sign, cx in ((-1, bx0 + 15), (1, bx1 - 15)):
                chevron(cx, y, sign)

                def cyc(s=sign, k=key, o=options):
                    i = (o.index(st.get(k, o[0])) if st.get(k) in o else 0)
                    st[k] = o[(i + s) % len(o)]
                hits.append((cx - 13, y - 14, cx + 13, y + 14, cyc))

        def fit_window(*_):
            """창이 화면 밖으로 나가 저장 버튼이 잘리지 않게 위치 보정."""
            if not win.winfo_exists():
                return
            win.update_idletasks()
            wh, ww = win.winfo_height(), win.winfo_width()
            sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
            px = min(max(self.root.winfo_rootx() - 70, 10), max(sw - ww - 10, 10))
            py = min(max(self.root.winfo_rooty() - 30, 10), max(sh - wh - 60, 10))
            win.geometry(f"+{int(px)}+{int(py)}")

        def text_w(t, font):
            tid = cv.create_text(-4000, -4000, text=t, font=font, anchor="w")
            x0, _, x1, _ = cv.bbox(tid)
            cv.delete(tid)
            return x1 - x0

        def fit_text(t, size, room, min_size):
            """상자 안에 들어가는 (글자, 글꼴). 줄여도 넘치면 끝을 잘라 …로."""
            t = str(t)
            n = size
            while n > min_size and text_w(t, (FONT, FS(n))) > room:
                n -= 1
            font = (FONT, FS(n))
            if text_w(t, font) <= room:
                return t, font
            while len(t) > 1 and text_w(t + "…", font) > room:
                t = t[:-1]
            return t + "…", font

        def open_picker(y, text, key, options):
            """눌러서 펼치는 목록 — 좌우로 넘기지 않고 전부 보여 준다.

            늘어난 높이를 돌려주면 group이 흰 카드를 그만큼 늘려 준다.
            """
            label(y, text)
            if not options:
                cv.create_text(RX, y, anchor="e", text="(없음)",
                               font=(FONT, FS(8)), fill=cd["sub"])
                return 0
            cur = st.get(key, options[0])
            if cur not in options:
                cur = options[0]
            bx0, bx1 = RX - 176, RX
            opened = (self._settings_open == key)
            rrect(bx0, y - 14, bx1, y + 14, 14, fill=SOFT,
                  outline=cd["border"], width=1)
            # 글자 수로 자르면 한글·괄호가 섞였을 때 상자 밖으로 넘친다.
            # 실제 폭을 재서 글꼴을 줄이고, 그래도 넘치면 끝을 자른다.
            room = (bx1 - 26) - (bx0 + 12)
            nm, nf = fit_text(cur, 8, room, 6)
            cv.create_text(bx0 + 12, y, anchor="w", text=nm,
                           font=nf, fill=cd["text"])
            ax, dy = bx1 - 15, (-3 if opened else 3)
            cv.create_line(ax - 5, y - dy, ax, y + dy, ax + 5, y - dy,
                           width=2, capstyle="round", joinstyle="round",
                           fill=cd["fill"])

            def flip(k=key):
                self._settings_open = None if self._settings_open == k else k
            hits.append((bx0, y - 14, bx1, y + 14, flip))
            if not opened:
                return 0
            ih = max(20, round(23 * self.ui_k))
            top = y + 16
            for i, opt in enumerate(options):
                iy = top + ih / 2 + i * ih
                on = (opt == cur)
                if on:
                    rrect(bx0, iy - ih / 2 + 2, bx1, iy + ih / 2 - 2, 9,
                          fill=cd["fill"], outline="")
                nm2, nf2 = fit_text(opt, 8, (bx1 - 14) - (bx0 + 14), 6)
                cv.create_text(bx0 + 14, iy, anchor="w", text=nm2,
                               font=(nf2[0], nf2[1], "bold") if on else nf2,
                               fill="#ffffff" if on else cd["text"])

                def pick(k=key, v=opt):
                    st[k] = v
                    self._settings_open = None
                hits.append((bx0, iy - ih / 2, bx1, iy + ih / 2, pick))
            return 16 + ih * len(options)

        def send_feedback():
            ok, msg = self._fb_send(fb_text.get("1.0", "end"))
            self._fb_msg = msg
            if ok:
                fb_text.delete("1.0", "end")

        def draw():
            cv.delete("all")
            hits.clear()
            sliders.clear()
            y = header(24)
            timer_rows = [
                lambda ry: stepper(ry, "목표 작업시간", "goal_hours", 0.5, 16, 0.5, "h"),
                lambda ry: stepper(ry, "휴식 전환", "idle_sec", 5, 600, 5, "초"),
                lambda ry: stepper(ry, "잠들기", "sleep_min", 1, 120, 1, "분"),
                lambda ry: open_picker(ry, "스트레칭 알림", "stretch_every",
                                       list(self.STRETCH_CHOICES)),
            ]
            if self.cfg.get("history"):
                timer_rows.append(
                    lambda ry: stepper(ry, "하루 바뀌는 시각", "day_start",
                                       0, 12, 1, "시"))
            timer_rows += [
                lambda ry: toggle(ry, "작업 타이머 표시", "show_timer"),
                lambda ry: toggle(ry, "작업 프로그램에서만 측정", "work_apps_only"),
            ]
            mons = self.monitor_names()
            if self.cfg.get("pen_monitor_pick") and len(mons) > 2:
                timer_rows.append(
                    lambda ry: open_picker(ry, "펜 따라갈 화면",
                                           "pen_monitor", mons))
            y = group(y, "타이머", timer_rows)
            y = group(y, "소리", [
                lambda ry: slider(ry, "타자 소리 볼륨", "sound_volume", 0, 100),
                lambda ry: slider(ry, "펜 소리 볼륨", "pen_volume", 0, 100),
                lambda ry: slider(ry, "클릭 소리 볼륨", "poke_volume", 0, 100),
                lambda ry: toggle(ry, "타자 소리", "sound"),
                lambda ry: open_picker(ry, "소리 팩", "sound_pack",
                                       self.sound_packs),
            ])
            disp = []
            if len(self.skins) > 1:
                disp.append(lambda ry: open_picker(ry, "패션", "skin",
                                                  self.skin_names))
            disp += [
                lambda ry: stepper(ry, "캐릭터 크기", "scale_pct", 50, 200, 10, "%"),
                lambda ry: stepper(ry, "글자 크기", "font_pct", 70, 160, 10, "%"),
                lambda ry: toggle(ry, "캐릭터 그림자", "shadow"),
                lambda ry: toggle(ry, "타블렛 낙서 표시", "trail"),
                lambda ry: toggle(ry, "항상 위에 표시", "topmost"),
            ]
            if getattr(sys, "frozen", False):
                disp.append(lambda ry: toggle(ry, "윈도우 시작 시 자동 실행",
                                              "autostart"))
            y = group(y, "표시", disp)

            cv.create_oval(PAD + 3, y - 4, PAD + 11, y + 4,
                           fill=cd["fill"], outline="")
            cv.create_text(PAD + 18, y, anchor="w", text="작업 프로그램",
                           font=(FONT, FS(9), "bold"), fill=cd["fill"])
            cv.create_text(W - PAD - 4, y, anchor="e", text="쉼표로 구분",
                           font=(FONT, FS(8)), fill=cd["sub"])
            y += 16
            rrect(PAD, y, W - PAD, y + 50, 16, fill="#ffffff",
                  outline=LINE, width=1)
            cv.create_window(LX, y + 13, anchor="nw", window=apps_entry,
                             width=W - PAD * 2 - IN * 2, height=24)
            y += 50 + 22


            if fb_on:
                cv.create_oval(PAD + 3, y - 4, PAD + 11, y + 4,
                               fill=cd["fill"], outline="")
                cv.create_text(PAD + 18, y, anchor="w",
                               text="건의 사항 · 버그 보내기",
                               font=(FONT, FS(9), "bold"), fill=cd["fill"])
                # 제목이 길어 오른쪽에 붙이면 겹친다 — 설명은 아랫줄로
                y += 15
                cv.create_text(PAD + 18, y, anchor="w",
                               text="불편한 점, 추가되었으면 하는 기능 등",
                               font=(FONT, FS(8)), fill=cd["sub"])
                y += 15
                rrect(PAD, y, W - PAD, y + 96, 16, fill="#ffffff",
                      outline=LINE, width=1)
                cv.create_window(LX, y + 12, anchor="nw", window=fb_text,
                                 width=W - PAD * 2 - IN * 2, height=52)
                sb = (W - PAD - IN - 92, y + 68, W - PAD - IN, y + 68 + 26)
                rrect(*sb, 13, fill=cd["fill"], outline="")
                cv.create_text((sb[0] + sb[2]) / 2, (sb[1] + sb[3]) / 2,
                               text="보내기", font=(FONT, FS(8), "bold"),
                               fill="#ffffff")
                cv.create_text(LX, (sb[1] + sb[3]) / 2, anchor="w",
                               text=self._fb_msg or "",
                               font=(FONT, FS(8)), fill=cd["sub"])
                hits.append((*sb, send_feedback))
                y += 96 + 22

            # 화면에 들어가는 만큼만 보여 주고 나머지는 스크롤로 넘긴다.
            # 창 높이를 내용에 맞춰 늘리기만 하면 아래가 잘려 저장을 못 누른다.
            room = self.root.winfo_screenheight() - self._ui(190)
            view_h = int(min(y, max(self._ui(240), room)))
            cv.config(height=view_h, scrollregion=(0, 0, W, y))
            scrolling = y > view_h + 1
            if scrolling:
                vbar.pack(side="right", fill="y")
            else:
                vbar.pack_forget()
                cv.yview_moveto(0)
            draw_bar(scrolling)
            # 목록을 펼치면 창 높이가 달라진다 — 화면 밖으로 나가지 않게 위치를
            # 다시 잡는다 (그리는 중에 재진입하지 않도록 예약)
            win.after_idle(fit_window)

        def draw_bar(scrolling):
            """아래에 늘 붙어 있는 띠 — 스크롤해도 저장 버튼이 사라지지 않는다."""
            bar.delete("all")
            bar_hits.clear()
            win.update_idletasks()
            tw = W + (vbar.winfo_reqwidth() if scrolling else 0)
            bar.config(width=tw, height=self._ui(78))
            bar.create_line(0, 1, tw, 1, fill=LINE)
            bar.create_text(tw / 2, self._ui(17),
                            text="패션 · 크기 · 타이머는 저장 시 재시작",
                            font=(FONT, FS(8)), fill=cd["sub"])
            by = self._ui(30)
            bx0, bx1 = tw / 2 - 64, tw / 2 + 64
            rrect(bx0, by, bx1, by + 40, 18, on=bar, fill=cd["fill"], outline="")
            bar.create_text(tw / 2, by + 20, text="저장",
                            font=(FONT, FS(10), "bold"), fill="#ffffff")
            bar_hits.append((bx0, by, bx1, by + 40, save))

        def set_slider(key, x, sx0, sx1, lo, hi):
            frac = min(1.0, max(0.0, (x - sx0) / max(sx1 - sx0, 1)))
            step = 5 if hi > 20 else 1
            st[key] = int(round((lo + (hi - lo) * frac) / step) * step)

        def on_bar_click(e):
            for x0, y0, x1, y1, fn in bar_hits:
                if x0 <= e.x <= x1 and y0 <= e.y <= y1:
                    fn()
                    return

        def on_wheel(e):
            cv.yview_scroll(-3 if e.delta > 0 else 3, "units")

        def on_click(e):
            e.y = int(cv.canvasy(e.y))       # 스크롤한 만큼 좌표를 맞춘다
            for x0, y0, x1, y1, fn in hits:
                if x0 <= e.x <= x1 and y0 <= e.y <= y1:
                    fn()
                    if win.winfo_exists():
                        draw()
                    return
            for sx0, sx1, sy, key, lo, hi in sliders:
                if sx0 - 12 <= e.x <= sx1 + 12 and sy - 14 <= e.y <= sy + 14:
                    set_slider(key, e.x, sx0, sx1, lo, hi)
                    draw()
                    return

        def on_drag(e):
            e.y = int(cv.canvasy(e.y))
            for sx0, sx1, sy, key, lo, hi in sliders:
                if sy - 16 <= e.y <= sy + 16:
                    set_slider(key, e.x, sx0, sx1, lo, hi)
                    draw()
                    return

        def save():
            new = dict(st)
            new["work_apps"] = apps_var.get().strip()
            new["goal_hours"] = float(new["goal_hours"])
            new["idle_sec"] = max(float(new["idle_sec"]), 5.0)
            new["sleep_min"] = max(1, int(new["sleep_min"]))
            new["day_start"] = max(0, min(12, int(new.get("day_start", 6))))
            new["scale_pct"] = max(50, min(200, int(new["scale_pct"])))
            new["font_pct"] = max(70, min(160, int(new["font_pct"])))
            for k in ("sound_volume", "pen_volume", "poke_volume"):
                new[k] = max(0, min(100, int(new[k])))
            need_restart = (new["scale_pct"] != self.us["scale_pct"]
                            or new["font_pct"] != self.us.get("font_pct", 100)
                            or new.get("skin") != self.us.get("skin")
                            or bool(new["show_timer"]) != self.timer_on
                            or bool(new["shadow"]) != bool(self.us.get("shadow", True)))
            self.us.update(new)
            self._save_settings()
            self.idle_thr = self.us["idle_sec"]
            self.root.attributes("-topmost", bool(self.us["topmost"]))
            self._init_sound()
            self._apply_autostart()
            win.destroy()
            if need_restart:
                self._restart()

        cv.bind("<Button-1>", on_click)
        cv.bind("<B1-Motion>", on_drag)
        bar.bind("<Button-1>", on_bar_click)
        for _w in (win, cv, bar):
            _w.bind("<MouseWheel>", on_wheel)
        draw()
        fit_window()


    def _sanitize_settings(self):
        """저장된 설정 값이 빈 문자열·null·엉뚱한 형이면 기본값으로 되돌린다.

        옛 설정 창은 텍스트 입력이라 ""가 저장될 수 있었고, 그대로 float()에
        들어가면 매 프레임 예외가 나 화면이 통째로 비어 버린다.
        """
        for k, dv in DEFAULT_SETTINGS.items():
            v = self.us.get(k, dv)
            if isinstance(dv, bool):
                self.us[k] = bool(v)
            elif isinstance(dv, (int, float)):
                try:
                    self.us[k] = type(dv)(float(v))
                except (TypeError, ValueError):
                    self.us[k] = dv
            elif isinstance(dv, str) and not isinstance(v, str):
                self.us[k] = dv
        self.us["sleep_min"] = max(1, int(self.us["sleep_min"]))
        self.us["idle_sec"] = max(5.0, float(self.us["idle_sec"]))
        self.us["goal_hours"] = max(0.5, float(self.us["goal_hours"]))
        self.us["scale_pct"] = max(50, min(200, int(self.us["scale_pct"])))
        self.us["font_pct"] = max(70, min(160, int(self.us.get("font_pct", 100))))

    def _save_settings(self):
        try:
            with open(self.settings_path, "w", encoding="utf-8") as fp:
                json.dump(self.us, fp, ensure_ascii=False, indent=1)
        except Exception:
            pass

    def _apply_autostart(self):
        """로그인 시 자동 실행 등록/해제 (배포본만). 윈도우=레지스트리, 맥=LaunchAgent."""
        if not getattr(sys, "frozen", False):
            return                       # 소스 실행(로컬)에서는 의미 없음
        if IS_MAC:
            return self._apply_autostart_mac()
        try:
            import winreg
            name = os.path.splitext(os.path.basename(sys.executable))[0]
            with winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                                r"Software\Microsoft\Windows\CurrentVersion\Run",
                                0, winreg.KEY_SET_VALUE) as key:
                if self.us.get("autostart", True):
                    winreg.SetValueEx(key, name, 0, winreg.REG_SZ,
                                      f'"{sys.executable}"')
                else:
                    try:
                        winreg.DeleteValue(key, name)
                    except FileNotFoundError:
                        pass
        except Exception:
            pass

    def _apply_autostart_mac(self):
        """~/Library/LaunchAgents 에 plist를 쓰거나 지운다 (맥 로그인 자동 실행)."""
        try:
            label = "com.ena.mascot." + self.char.replace("parts_", "")
            d = os.path.expanduser("~/Library/LaunchAgents")
            path = os.path.join(d, label + ".plist")
            if not self.us.get("autostart", True):
                if os.path.exists(path):
                    os.remove(path)
                return
            os.makedirs(d, exist_ok=True)
            app = sys.executable                  # .app 번들이면 open -a 로 실행
            while app and app != "/" and not app.endswith(".app"):
                app = os.path.dirname(app)
            args = ["/usr/bin/open", "-a", app] if app.endswith(".app")                 else [sys.executable]
            out = ['<?xml version="1.0" encoding="UTF-8"?>',
                   '<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN"'
                   ' "http://www.apple.com/DTDs/PropertyList-1.0.dtd">',
                   '<plist version="1.0">', '<dict>',
                   "    <key>Label</key>", f"    <string>{label}</string>",
                   "    <key>ProgramArguments</key>", "    <array>"]
            out += [f"        <string>{a}</string>" for a in args]
            out += ["    </array>", "    <key>RunAtLoad</key>", "    <true/>",
                    "</dict>", "</plist>", ""]
            with open(path, "w", encoding="utf-8") as fp:
                fp.write(os.linesep.join(out))
        except Exception:
            pass


    def _restart(self):
        import subprocess
        if self.timer_on:
            self._timer_save()
        if getattr(sys, "frozen", False):
            subprocess.Popen([sys.executable])
        else:
            subprocess.Popen([sys.executable, os.path.abspath(__file__),
                              "--char", self.char_arg])
        self.close()

    # ── 프리뷰 ───────────────────────────────────────────────────────────
    def _preview_shots(self):
        from PIL import ImageGrab
        shots = [
            (f"preview_{self.char}_idle.png", {}),
            (f"preview_{self.char}_typing.png", {"type": True}),
            (f"preview_{self.char}_pen.png", {"pen": (0.35, 0.45)}),
            (f"preview_{self.char}_pen_corner.png", {"pen": (0.02, 0.95)}),
            (f"preview_{self.char}_blink.png", {"blink": True}),
            (f"preview_{self.char}_sleep.png", {"sleep": True}),
        ]
        for name, force in shots:
            self._force = force
            if force.get("type"):
                self.key_ang = 5.0
                self.pen_ang = -4.0
            if "pen" in force:
                self._pen_xy = list(self._quad_xy(*force["pen"]))
                self.strokes = [[self._quad_xy(0.25 + 0.15 * i, 0.35 + 0.12 * (i % 2))
                                 for i in range(5)]]
            self.draw(time.time())
            self.root.update()
            time.sleep(0.15)
            x, y = self.root.winfo_rootx(), self.root.winfo_rooty()
            ImageGrab.grab(bbox=(x, y, x + self.W, y + self.H)).save(
                os.path.join(HERE, name))
            print("saved", name)
        self.close()

    def _mac_log(self, text):
        """맥 창 설정 진단 기록 — 초기화 중이라 _log_error를 못 쓰는 구간용."""
        try:
            with open(os.path.join(self.state_dir, ".macwindow.log"), "a",
                      encoding="utf-8") as fp:
                fp.write(time.strftime("%Y-%m-%d %H:%M:%S ") + text + os.linesep)
        except Exception:
            pass

    def _setup_mac_window(self):
        """맥 투명 창 설정.

        캔버스를 MAC_KEY 로 칠하고, 그 색은 나중에 _mac_chroma_key() 가 합성 단계에서
        지운다. systemTransparent 를 쓰지 않는 이유는 _MacChromaKey 설명 참고 —
        Tk 9 가 그 색을 불투명한 검정으로 칠해 버린다.
        """
        mode = os.environ.get("MASCOT_MAC_MODE", "chroma")
        try:
            if mode == "opaque":                     # 대조군 (확실히 보임)
                self.root.config(bg="#808080")
                return "#808080"
            if mode == "legacy":                     # 예전 방식 (검은 사각형 재현용)
                self.root.attributes("-transparent", True)
                self.root.config(bg="systemTransparent")
                return "systemTransparent"
            self.root.attributes("-transparent", True)   # 기본 = 색상키 방식
            self.root.config(bg=MAC_KEY)
            return MAC_KEY
        except Exception as e:
            self._mac_log(f"[{mode}] 창 설정 실패 → {e!r}")
            return MAC_KEY

    def _mac_borderless(self):
        """맥에서 제목 표시줄 제거 — Tk 9는 overrideredirect만으로는 안 되는 경우가 있다."""
        if not IS_MAC:
            return
        try:
            self.root.update_idletasks()
            self.root.overrideredirect(False)
            self.root.overrideredirect(True)
        except Exception:
            pass
        try:                                   # 그래도 남으면 AppKit으로 직접
            from AppKit import NSApp
            self.root.update_idletasks()
            for w in self._mac_windows():
                try:
                    w.setStyleMask_(0)         # NSWindowStyleMaskBorderless
                    w.setHasShadow_(False)
                    w.setMovableByWindowBackground_(False)
                except Exception as e:
                    self._mac_log(f"창 설정 실패 → {e!r}")
            self._mac_keep_transparent()
            # 창이 화면에 올라온 뒤 되돌아가는 경우가 있고, 말풍선·할 일 패널은
            # 나중에 생기므로 계속 다시 걸어 준다.
            self.root.after(300, self._mac_keep_transparent)
            self.root.after(1500, self._mac_verify)
            for i, w in enumerate(NSApp.windows()):
                try:
                    bc = w.backgroundColor()
                    self._mac_log(
                        f"창{i}: 불투명={bool(w.isOpaque())} "
                        f"창알파={float(w.alphaValue()):.2f} "
                        f"배경알파={float(bc.alphaComponent()):.2f} "
                        f"크기={int(w.frame().size.width)}x{int(w.frame().size.height)}")
                except Exception as e:
                    self._mac_log(f"창{i} 상태 읽기 실패 → {e!r}")
            self._mac_log(self._mac_env())
        except Exception as e:
            self._mac_log(f"AppKit 접근 실패 → {e!r}")

    def _mac_windows(self):
        """이 프로그램의 마스코트 창만 고른다 (다른 창은 건드리지 않는다)."""
        from AppKit import NSApp
        out, other = [], []
        for w in NSApp.windows():
            try:
                sz = w.frame().size
                if abs(sz.width - self.W) <= 2 and abs(sz.height - self.H) <= 2:
                    out.append(w)
                elif sz.width > 4 and sz.height > 4:
                    other.append(int(sz.width))
            except Exception:
                pass
        if not out:                    # 크기로 못 찾으면 예전처럼 전부
            if not getattr(self, "_mac_miss_logged", False):
                self._mac_miss_logged = True       # 주기 호출이라 한 번만 남긴다
                self._mac_log(f"크기 {self.W}x{self.H} 창을 못 찾음 — 전체 적용")
            return list(NSApp.windows())
        if other and not getattr(self, "_mac_win_logged", False):
            self._mac_win_logged = True        # 주기 호출이라 한 번만 남긴다
            self._mac_log(f"건드리지 않은 다른 창 폭: {other}")
        return out

    def _mac_clear_bg(self):
        """마스코트 창을 투명하게 (표시 후 되돌아가는 것 대비해 여러 번 호출)."""
        if self.canvas_bg == "#808080":
            return
        try:
            from AppKit import NSColor
            clear = NSColor.clearColor()
            for w in self._mac_windows():
                try:
                    w.setOpaque_(False)
                    w.setBackgroundColor_(clear)
                    # 창을 투명하게 해도 그 위를 덮는 뷰가 스스로 배경을 칠하면
                    # 소용이 없다. 캔버스가 그려지는 뷰의 레이어까지 비운다.
                    cv = w.contentView()
                    if cv is not None:
                        cv.setWantsLayer_(True)
                        lay = cv.layer()
                        if lay is not None:
                            lay.setBackgroundColor_(clear.CGColor())
                            lay.setOpaque_(False)
                except Exception as e:
                    self._mac_log(f"뷰 레이어 투명화 실패 → {e!r}")
        except Exception as e:
            self._mac_log(f"투명 재적용 실패 → {e!r}")

    def _mac_chroma_key(self):
        """캔버스에 칠해진 MAC_KEY 색을 합성 단계에서 지운다 (실제 투명화 담당)."""
        if self.canvas_bg != MAC_KEY:
            return 0                       # opaque·legacy 모드에서는 걸지 않는다
        ck = getattr(self, "_mac_ck", None)
        if ck is None:
            ck = self._mac_ck = _MacChromaKey(MAC_KEY)
            if ck.err:
                self._mac_log(f"색상키 준비 실패 → {ck.err}")
            else:
                self._mac_log(f"색상키 준비됨: {MAC_KEY} 격자={ck.key_idx} "
                              f"큐브={ck.N}^3 반경={ck.RAD}")
        return ck.apply_all()

    def _mac_keep_transparent(self):
        """투명 설정을 다시 못 박는다. 창이 나중에 더 생기므로 주기적으로 돈다."""
        try:
            self._mac_clear_bg()
            n = self._mac_chroma_key()
            if n:
                self._mac_log(f"색상키 적용한 창 수: {n}")
        except Exception as e:
            self._mac_log(f"투명 유지 실패 → {e!r}")
        try:
            self.root.after(2000, self._mac_keep_transparent)
        except Exception:
            pass

    def _mac_verify(self):
        """정말 투명해졌는지 화면 합성 결과를 직접 읽어 기록한다.

        캐릭터가 없는 구석을 찍는다. 알파가 0 이면 성공, 255 면 여전히 덮여 있는 것.
        """
        ck = getattr(self, "_mac_ck", None)
        if ck is None or ck.err:
            return
        pts = [(4, 4), (self.W - 5, 4), (4, self.H - 5)]
        r = ck.probe(self.W, pts)
        if not r:
            self._mac_log(f"합성 결과 확인 실패 → {ck.err}")
            return
        got = ["없음" if p is None else
               ("투명" if p[0] == 0 else f"불투명{p[1:]}") for p in r["px"]]
        self._mac_log(f"합성 결과(배율 {r['scale']:.0f}x) 좌상/우상/좌하 = "
                      + " · ".join(got))

    def _mac_env(self):
        """투명이 안 될 때 원인을 가르는 정보 — Tk 색상 처리 · 시스템 설정."""
        out = [f"canvas_bg={self.canvas_bg!r}"]
        try:
            out.append("tk=" + str(self.root.tk.call("info", "patchlevel")))
        except Exception as e:
            out.append(f"tk오류={e!r}")
        try:
            out.append("transparent속성=" + str(self.root.attributes("-transparent")))
        except Exception as e:
            out.append(f"transparent속성오류={e!r}")
        # 참고: winfo_rgb 는 알파를 버리므로 systemTransparent 가 흰색으로 보이지만,
        # 실제로 칠해지는 값은 불투명한 검정이다. 판단은 _mac_verify() 의 합성 결과로.
        try:
            out.append("systemTransparent해석=" +
                       str(self.root.winfo_rgb("systemTransparent")))
        except Exception as e:
            out.append(f"systemTransparent오류={e!r}")
        ck = getattr(self, "_mac_ck", None)
        out.append("색상키=" + (f"{MAC_KEY} 준비됨" if ck and not ck.err
                                else f"실패({ck.err})" if ck else "미준비"))
        try:
            out.append("캔버스실제bg=" + str(self.canvas.cget("bg")))
        except Exception as e:
            out.append(f"캔버스bg오류={e!r}")
        try:                       # 시스템 설정에서 투명 효과를 끈 경우
            from AppKit import NSWorkspace
            ws = NSWorkspace.sharedWorkspace()
            out.append("투명도줄이기=" +
                       str(bool(ws.accessibilityDisplayShouldReduceTransparency())))
        except Exception as e:
            out.append(f"투명도줄이기확인불가={e!r}")
        return " | ".join(out)

    def _dump_debug(self):
        """맥 진단용 상태 덤프 — 그림이 안 보일 때 원인 좁히기."""
        try:
            lines = [f"platform: win={IS_WIN} mac={IS_MAC}",
                     f"geometry: {self.root.winfo_geometry()} "
                     f"W={self.W} H={self.H} oy={self.oy} scale={self.s:.3f}",
                     f"canvas bg={self.canvas_bg} items={len(self.canvas.find_all())}",
                     f"parts_dir={self.parts_dir}",
                     f"loaded images={sorted(self.im)}"]
            for name in sorted(self.im):
                im = self.im[name]
                lines.append(f"  {name}: {im.width()}x{im.height()}")
            kinds = {}
            for it in self.canvas.find_all():
                k = self.canvas.type(it)
                kinds[k] = kinds.get(k, 0) + 1
            lines.append(f"canvas item kinds: {kinds}")
            for it in self.canvas.find_all():
                if self.canvas.type(it) == "image":
                    lines.append(f"  image at {self.canvas.coords(it)} "
                                 f"state={self.canvas.itemcget(it, 'state')!r}")
            with open(os.path.join(self.state_dir, "debug.txt"), "w",
                      encoding="utf-8") as fp:
                fp.write(os.linesep.join(lines))
        except Exception:
            import traceback
            with open(os.path.join(self.state_dir, "debug.txt"), "w",
                      encoding="utf-8") as fp:
                traceback.print_exc(file=fp)

    def run(self):
        self.root.mainloop()


def _arg(name, default):
    if name in sys.argv:
        i = sys.argv.index(name)
        if i + 1 < len(sys.argv):
            return sys.argv[i + 1]
    return default


if __name__ == "__main__":
    _char = _arg("--char", "parts")
    if "--preview" not in sys.argv and already_running(os.path.basename(_char)):
        sys.exit(0)                 # 같은 캐릭터가 이미 떠 있으면 조용히 종료
    Mascot(char_dir=_char, preview="--preview" in sys.argv).run()
