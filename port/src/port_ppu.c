/*
 * Software GBA PPU.
 *
 * Renders the picture described by the I/O registers, palette, VRAM and OAM
 * into a 32-bit frame buffer. The output can be larger than the GBA's
 * 240x160: GBA pixel (0,0) is placed at (originX, originY) and background
 * layers, sprites and full-screen windows continue past the original edges
 * when the current scene supports a wide view (gPortScreen.wide).
 *
 * Per-line state changes (HBlank interrupts and HBlank DMA) are honoured for
 * the 160 original lines; lines added above and below reuse the state of the
 * nearest original line.
 */
#include <math.h>
#include <string.h>
#include <stdlib.h>

#include "port/port.h"
#include "port/port_hd2d.h"
#include "engine.h"
#include "port/port_state.h"

extern const void* gMsgwinMapBlocks[4];

PortScreen gPortScreen = { GBA_SCREEN_W, GBA_SCREEN_H, 0, 0, 0 };

/* Area the game should keep sprites alive in (see VIEW_* in gba/defines.h). */
int gPortViewLeft = 0;
int gPortViewTop = 0;
int gPortViewRight = GBA_SCREEN_W;
int gPortViewBottom = GBA_SCREEN_H;

/* Full-range sprite positions written alongside OAM by UpdateSpriteOam. */
typedef struct OamExt {
    int16_t x;
    int16_t y;
} OamExt;
static OamExt sOamExt[128];

/* Map-block backgrounds as they were when the scroll registers were last
   committed: lets the wide view draw the world beyond the VRAM window. */
typedef struct BgLatch {
    void* const* map;
    int width;
    int height;
    int x;
    int y;
    uint16_t hofs;
    uint16_t vofs;
    int valid;
} BgLatch;
static BgLatch sBgLatch[4];

/* Display offsets requested by the game for docking UI (see engine.h). */
int gPortSpriteShiftX;
typedef struct BgWorld {
    PortWorldTileFunc fn;
    int x;
    int y;
    uint16_t hofs;
    uint16_t vofs;
    int valid;
} BgWorld;
static BgWorld sBgWorld[4];
static BgWorld sBgWorldLatched[4];

void PortSetBgWorld(int bg, PortWorldTileFunc fn, int originX, int originY) {
    if (bg >= 0 && bg < 4) {
        sBgWorld[bg].fn = fn;
        sBgWorld[bg].x = originX;
        sBgWorld[bg].y = originY;
    }
}

static int sBgShift[4];
static int sBgShiftLatched[4];
static int sBgDocked[4];
static int sBgDockedLatched[4];
static int sBattleView;
static int sArenaBands[6]; /* bounds, left source/width, right source/width */
typedef struct BgTextTile {
    uint16_t code;
    uint8_t style, faceIndex, shadowIndex, panelIndex;
    uint8_t cap, base; /* rows of the digit's ink: height and baseline */
    uint8_t source[32];
} BgTextTile;
static BgTextTile sBgTextTiles[2048];
typedef struct BgTextGlyph {
    PortTextGlyph glyph;
    uint8_t bg, priority, screen;
} BgTextGlyph;
static BgTextGlyph sBgTextGlyphs[1024];
static int sBgTextCount;

void PortClearBgTextTiles(void) { memset(sBgTextTiles, 0, sizeof(sBgTextTiles)); }

void PortRegisterBgTextTile(void* address, int code, int style, const void* source32) {
    uintptr_t offset = (uintptr_t)address - GBA_VRAM;
    BgTextTile* tile;
    if (offset >= 0x10000 || (offset & 31) || !source32) return;
    tile = &sBgTextTiles[offset / 32];
    tile->code = (uint16_t)code;
    tile->style = (uint8_t)style;
    tile->faceIndex = (uint8_t)((style & 0xFF00) ? (style >> 8) & 15 : 15);
    tile->shadowIndex = (uint8_t)((style & 0xFF00) ? (style >> 12) & 15 : 14);
    tile->panelIndex = (uint8_t)((style & 0xFF00) ? (style >> 16) & 15 : 13);
    if (!(style & 0xFF00)) {
        /* The tile's own colours: the commonest index is the panel behind the
           digit, the next ones its face and shadow. Greyed-out panels use
           other indices than the active ones, so a fixed choice would not
           match what the cartridge shows. */
        int count[16] = { 0 }, order[3] = { -1, -1, -1 }, i, k;
        for (i = 0; i < 32; i++) {
            count[((const uint8_t*)source32)[i] & 15]++;
            count[((const uint8_t*)source32)[i] >> 4]++;
        }
        for (k = 0; k < 3; k++)
            for (i = 1; i < 16; i++)
                if (count[i] && i != order[0] && i != order[1] && (order[k] < 0 || count[i] > count[order[k]]))
                    order[k] = i;
        if (order[1] >= 0) {
            tile->panelIndex = (uint8_t)order[0];
            tile->faceIndex = (uint8_t)order[1];
            tile->shadowIndex = (uint8_t)(order[2] >= 0 ? order[2] : order[0]);
        }
    }
    {
        /* Measure the selected ink, including callers with explicit palette
           indices. A dense digit can have more shadow than panel pixels;
           frequency is not a safe way to identify those numeric families. */
        int top = 8, bottom = -1, y, xx;
        for (y = 0; y < 8; y++) for (xx = 0; xx < 8; xx++) {
            uint8_t v = ((const uint8_t*)source32)[y * 4 + xx / 2];
            int c = (xx & 1) ? v >> 4 : v & 15;
            if (c && c != tile->panelIndex &&
                (c == tile->faceIndex || c == tile->shadowIndex)) {
                if (y < top) top = y;
                if (y > bottom) bottom = y;
            }
        }
        tile->cap = bottom > top ? (uint8_t)(bottom - top) : 0;
        tile->base = bottom > top ? (uint8_t)bottom : 0;
    }
    memcpy(tile->source, source32, 32);
}

/* A docked layer is screen UI moved toward an edge: it shows only what the
   hardware would (no world-map continuation), so parked windows stay hidden. */
static unsigned sScreenBgMask;
static int sBgSplit[4]; /* PortBgSplit, below */
static int sBgSplitBands[4]; /* repeat authored ornamental tiles in the split gap */
static int sBgClip[4]; /* PortBgClip: UI layer kept to the GBA columns */
typedef struct MenuBandSource {
    const uint16_t* frame;
    const ObjTiles* tiles;
    const ObjPalette* palette;
    int y;
} MenuBandSource;
/* The menu assets the margins carry on (header, bands, tabs). The game sets
   them while it draws a frame, but that frame's sprites reach the screen
   only after the next VBlank: the margins use the values latched with them
   (PortMenuLatch), so they never run a frame ahead of the picture (the
   extensions blinked while a menu slid in or out). */
typedef struct MenuSources {
    const uint16_t* headerFrame;
    const ObjTiles* headerTiles;
    const ObjPalette* headerPalette;
    MenuBandSource bands[2];
    const uint16_t* tabFrame;
    const ObjTiles* tabTiles;
    const ObjPalette* tabPalette;
    int tabBg[2], tabX[2], tabY[2];
    int headerX, headerDrawn;
} MenuSources;
static MenuSources sMenuShown = { .tabBg = { -1, -1 } }, sMenuPend = { .tabBg = { -1, -1 } };
#define sMenuHeaderFrame sMenuShown.headerFrame
#define sMenuHeaderTiles sMenuShown.headerTiles
#define sMenuHeaderPalette sMenuShown.headerPalette
#define sMenuBands sMenuShown.bands
#define sMenuTabFrame sMenuShown.tabFrame
#define sMenuTabTiles sMenuShown.tabTiles
#define sMenuTabPalette sMenuShown.tabPalette
#define sMenuTabBg sMenuShown.tabBg
#define sMenuTabX sMenuShown.tabX
#define sMenuTabY sMenuShown.tabY

/* VBlank: the sprites drawn this frame go on screen; so do their sources */
static uint32_t sMenuModeStart, sMenuHeaderMoved;
void PortMenuLatch(void) {
    if (sMenuPend.headerX != sMenuShown.headerX || sMenuPend.headerDrawn != sMenuShown.headerDrawn)
        sMenuHeaderMoved = PortFrameCount();
    sMenuShown = sMenuPend;
    sMenuPend.headerDrawn = 0;
}

/* a menu sliding in (its first frames) or out (its header moving) */
int PortMenuSliding(void) {
    uint32_t now = PortFrameCount();
    return now - sMenuModeStart < 45 || now - sMenuHeaderMoved < 8;
}
static int sSceneNarrow, sNarrowWanted, sNarrowWait; /* PortSceneNarrow, below */
static int sSpotlight;
void PortSetSpotlight(int active) { sSpotlight = active; }
int PortSpotlightActive(void) { return sSpotlight; }
void PortPpuVisitState(PortStateVisitor visit) {
    visit(sBgLatch, sizeof(sBgLatch));
    visit(sBgShift, sizeof(sBgShift));
    visit(sBgShiftLatched, sizeof(sBgShiftLatched));
    visit(sBgDocked, sizeof(sBgDocked));
    visit(sBgDockedLatched, sizeof(sBgDockedLatched));
    visit(&sBattleView, sizeof(sBattleView));
    visit(sArenaBands, sizeof(sArenaBands));
    visit(sBgTextTiles, sizeof(sBgTextTiles));
    visit(sOamExt, sizeof(sOamExt));
    visit(sBgWorld, sizeof(sBgWorld));
    visit(sBgWorldLatched, sizeof(sBgWorldLatched));
    visit(sBgSplit, sizeof(sBgSplit));
    visit(&sScreenBgMask, sizeof(sScreenBgMask));
    visit(sBgSplitBands, sizeof(sBgSplitBands));
    visit(sBgClip, sizeof(sBgClip));
    visit(&sSceneNarrow, sizeof(sSceneNarrow));
    visit(&sNarrowWanted, sizeof(sNarrowWanted));
    visit(&sNarrowWait, sizeof(sNarrowWait));
    visit(&sSpotlight, sizeof(sSpotlight));
    visit(&sMenuShown, sizeof(sMenuShown));
    visit(&sMenuPend, sizeof(sMenuPend));
}

void PortSetBgShiftX(int bg, int shift) {
    if (bg >= 0 && bg < 4) {
        sBgShift[bg] = shift;
        sBgDocked[bg] = 0;
    }
}

void PortDockBg(int bg, int shift) {
    if (bg >= 0 && bg < 4) {
        sBgShift[bg] = shift;
        sBgDocked[bg] = 1;
    }
}

int PortWideMarginX(void) {
    return gPortScreen.wide ? gPortScreen.originX : 0;
}

int gPortSpriteShiftY;

int PortWideMarginY(void) {
    return gPortScreen.wide ? gPortScreen.originY : 0;
}

/* Anchors nest (a HUD task may draw child tasks), so keep a small stack. */
static int sHudStack[16][4];
static int sHudDepth;
static int sHudAx, sHudAy;

void PortHudBegin(int ax, int ay) {
    if (sHudDepth < 16) {
        sHudStack[sHudDepth][0] = gPortSpriteShiftX;
        sHudStack[sHudDepth][1] = gPortSpriteShiftY;
        sHudStack[sHudDepth][2] = sHudAx;
        sHudStack[sHudDepth][3] = sHudAy;
    }
    sHudDepth++;
    sHudAx = ax;
    sHudAy = ay;
    /* ax 2: the HUD's scale, but placed where the world puts it (the
       enemy's card follows its enemy across the arena) */
    gPortSpriteShiftX = (ax == 2 ? 0 : ax) * PortWideMarginX();
    gPortSpriteShiftY = ay * PortWideMarginY();
}

int gPortWorldScale; /* the world's pixel scale (presenter), for ax 2 */

/* x on the HUD canvas of a world-placed sprite (ax 2): its centre stays
   over the same window point as in the world picture */
static int HudWorldX(int ox, int bw, int w) {
    int hs = gPortHudScale > 0 ? gPortHudScale : 1, ws = gPortWorldScale > 0 ? gPortWorldScale : hs;
    int centre = ox + bw / 2 + gPortScreen.originX - gPortScreen.width / 2;
    return w / 2 + centre * ws / hs - bw / 2;
}

void PortHudEnd(void) {
    if (sHudDepth > 0)
        sHudDepth--;
    if (sHudDepth < 16) {
        gPortSpriteShiftX = sHudStack[sHudDepth][0];
        gPortSpriteShiftY = sHudStack[sHudDepth][1];
        sHudAx = sHudStack[sHudDepth][2];
        sHudAy = sHudStack[sHudDepth][3];
    }
}

/* Pointers/highlights that refer to HUD elements: anchor by screen zone,
   matching the corners the HUD itself is docked to. */
void PortHudBeginAt(int x, int y) {
    int ax = x < 80 ? -1 : (x >= 160 ? 1 : 0);
    int ay = y < 54 ? -1 : (y >= 80 ? 1 : 0);

    PortHudBegin(ax, ay);
}

/* Which sprite entries / OAM slots belong to the HUD, and their anchor. */
typedef struct SpriteTag {
    uint8_t hud;
    int8_t ax;
    int8_t ay;
    uint16_t text; /* HD text: pixel-font character (Shift-JIS in Japanese), 0 for other sprites */
    uint8_t style; /* HD text font: 0 dialogue / menu, 1 movie subtitles */
    uint8_t screen; /* drawn by a menu: goes on the screen layer */
    uint8_t header; /* a menu header (DrawMenuHeader) */
    uint8_t hdHudPart; /* HD enemy panel: frame, cap, live bar */
    uint8_t digit;
} SpriteTag;
static SpriteTag sEntryTag[128];
static SpriteTag sOamTag[128];
static int sHudLayer;
static int sHdText;
int gPortHdHudPart;
int gPortHudDigit;
static PortHudDigit* sHudDigits;
static int sHudDigitCount;
static uint8_t* sHudDigitOwners;
static size_t sHudDigitOwnerSize;
static uint8_t* sEnemyBarMask;
static size_t sEnemyBarMaskSize;
static int sEnemyBarRect[4], sEnemyBarSlot;
static uint32_t sEnemyBarRows[32];
static uint8_t* sPlayerBarMask;
static size_t sPlayerBarMaskSize;
static int sPlayerBarRect[4], sPlayerBarSlot;
static uint32_t sPlayerBarRows[32];
static int sPlayerFullHp;
int PortPpuPlayerHudFullHp(void) { return sPlayerFullHp; }
static int sPlayerFrameRect[4];
int PortPpuPlayerHudFrame(int* rect) {
    if (sPlayerFrameRect[2] < sPlayerFrameRect[0]) return 0;
    memcpy(rect, sPlayerFrameRect, sizeof(sPlayerFrameRect));
    return 1;
}
int PortPpuPlayerHudBar(int* rect, uint32_t* rows) {
    if (sPlayerBarRect[2] < sPlayerBarRect[0]) return 0;
    memcpy(rect, sPlayerBarRect, sizeof(sPlayerBarRect));
    memcpy(rows, sPlayerBarRows, sizeof(sPlayerBarRows));
    return 1;
}
int PortPpuPlayerHudBarVisible(int x, int y) {
    int front;
    if (!sPlayerBarMask || !sHudDigitOwners || x < 0 || y < 0 || x >= gPortHudW || y >= 32) return 0;
    front = sHudDigitOwners[y * gPortHudW + x];
    return sPlayerBarMask[y * gPortHudW + x] && (front == 0 || front >= sPlayerBarSlot + 1);
}
int PortPpuEnemyHudBar(int* rect, uint32_t* rows) {
    if (sEnemyBarRect[2] < sEnemyBarRect[0]) return 0;
    memcpy(rect, sEnemyBarRect, sizeof(sEnemyBarRect));
    memcpy(rows, sEnemyBarRows, sizeof(sEnemyBarRows));
    return 1;
}
int PortPpuEnemyHudBarVisible(int x, int y) {
    int at = y * gPortHudW + x, front;
    if (!sEnemyBarMask || !sHudDigitOwners || x < 0 || y < 0 || x >= gPortHudW || y >= gPortHudH) return 0;
    front = sHudDigitOwners[at];
    return sEnemyBarMask[at] && (front == 0 || front >= sEnemyBarSlot + 1);
}
int PortPpuHudDigits(PortHudDigit* out, int max) {
    int n = sHudDigitCount < max ? sHudDigitCount : max;
    if (n) memcpy(out, sHudDigits, n * sizeof(*out));
    return n;
}
int PortPpuHudDigitVisible(int digit, int x, int y) {
    int front;
    if (!sHudDigitOwners || digit >= sHudDigitCount || x < 0 || y < 0 || x >= gPortHudW || y >= gPortHudH)
        return 0;
    front = sHudDigitOwners[y * gPortHudW + x];
    return front == 0 || front >= sHudDigits[digit].slot + 1;
}
int PortPpuHudSpriteVisible(int slot, int x, int y) {
    int front;
    if (!sHudDigitOwners || x<0 || y<0 || x>=gPortHudW || y>=gPortHudH) return 0;
    front=sHudDigitOwners[y*gPortHudW+x];
    return front != 0 && front >= slot+1;
}
static int sEnemyHudRect[4]; /* left, top, right, bottom in HUD pixels */
static int sEnemyLabelRect[4];
static uint32_t sEnemyLabelColor;
int PortPpuEnemyHudLabel(int* rect, uint32_t* color) {
    if (sEnemyLabelRect[2] < sEnemyLabelRect[0]) return 0;
    memcpy(rect, sEnemyLabelRect, sizeof(sEnemyLabelRect));
    *color = sEnemyLabelColor;
    return 1;
}
int PortPpuEnemyHudRect(int* rect) {
    if (sEnemyHudRect[2] < sEnemyHudRect[0]) return 0;
    memcpy(rect, sEnemyHudRect, sizeof(sEnemyHudRect));
    return 1;
}
int gPortTextChar;
int gPortTextStyle;

/* ---- screen layer ---------------------------------------------------------------
 * Menus over the world (pause, save, world select, level up): their sprites
 * (drawn between PortScreenBegin/End) and the layers that are not world maps
 * are composed into gPortOverlay, gPortOverlayW x 160, which the presenter
 * scales to the window's height; the world keeps its own scale underneath.
 * The game marks every frame it draws such a menu.
 */
uint32_t gPortOverlay[PORT_MAX_W * GBA_SCREEN_H];
int gPortOverlayW = GBA_SCREEN_W;
int gPortScreenLayer; /* this frame uses the screen layer (set by the presenter) */
static int sScreenDepth, sScreenMark, sOverlay;
static int sScreenBg[4];
void PortScreenBg(int bg, int on) {
    if ((unsigned)bg < 4) {
        if (on) sScreenBgMask |= 1u << bg;
        else sScreenBgMask &= ~(1u << bg);
    }
}
static uint16_t sScrLine[PORT_MAX_W];
static uint8_t sScrPrio[PORT_MAX_W];
static uint8_t sScrIndex[PORT_MAX_W];
static uint8_t sScreenOccBg[PORT_MAX_W * GBA_SCREEN_H];
static uint8_t sScreenOccBgLayer[PORT_MAX_W * GBA_SCREEN_H];
static uint16_t sScreenOccObj[PORT_MAX_W * GBA_SCREEN_H];
static uint8_t sScrSemi[PORT_MAX_W];

void PortScreenBegin(void) {
    sScreenDepth++;
    sScreenMark = 1;
}

void PortScreenEnd(void) {
    if (sScreenDepth > 0)
        sScreenDepth--;
}

int PortTakeScreenMark(void) {
    int m = sScreenMark;
    sScreenMark = 0;
    return m;
}

/* Screen-layer BG split (as in the Vita port): the columns left of `column`
   move into the left margin, the rest into the right one. 0: off. */

void PortBgSplit(int bg, int column) {
    if (bg >= 0 && bg < 4)
        sBgSplit[bg] = column;
}

int PortScreenMarginX(void) {
    return (gPortOverlayW - GBA_SCREEN_W) / 2;
}

int gPortHudScale;
int gPortHeaderDraw;
static int HeaderBandColor(int y, int phase);
int gPortHudW;
int gPortHudH;

void PortSpriteTag(int entry) {
    if (entry >= 0 && entry < 128) {
        sEntryTag[entry].hud = sHudDepth > 0;
        sEntryTag[entry].ax = (int8_t)sHudAx;
        sEntryTag[entry].ay = (int8_t)sHudAy;
        sEntryTag[entry].text = (uint16_t)gPortTextChar;
        sEntryTag[entry].style = (uint8_t)gPortTextStyle;
        sEntryTag[entry].screen = sScreenDepth > 0;
        sEntryTag[entry].header = gPortHeaderDraw != 0;
        sEntryTag[entry].hdHudPart = (uint8_t)gPortHdHudPart;
        sEntryTag[entry].digit = (uint8_t)gPortHudDigit;
    }
}

void PortOamTagsReset(void) {
    memset(sOamTag, 0, sizeof(sOamTag));
}

/* Characters the outline font draws: printable Windows-1252 codes. The codes
   below 0x20 are icons (arrows, button shapes) and stay pixel art. */
static int HdTextGlyph(int oamIndex) {
    int c = sOamTag[oamIndex].text;

    if (!sHdText || c <= 0x20 || c == 0x7F)
        return 0;
    if (c > 0xFF) /* Shift-JIS (Japanese version); 0x8140 is the wide space */
        return c >= 0x8141;
    return c != 0x81 && c != 0x8D && c != 0x8F && c != 0x90 && c != 0x9D;
}

/* HD text for sprites written straight into OAM (movie subtitles). */
void PortOamSetText(int oamIndex, int code, int style) {
    if (oamIndex >= 0 && oamIndex < 128) {
        memset(&sOamTag[oamIndex], 0, sizeof(sOamTag[0]));
        /* Cartridge horizontal bar is glyph 25, below printable Latin.
           Subtitle punctuation belongs in the HD line, unlike button icons. */
        sOamTag[oamIndex].text = (uint16_t)(style == 1 && code == 25 ? 0x97 : code);
        sOamTag[oamIndex].style = (uint8_t)style;
    }
}

void PortOamSetSource(int oamIndex, int entry) {
    if (oamIndex >= 0 && oamIndex < 128 && entry >= 0 && entry < 128)
        sOamTag[oamIndex] = sEntryTag[entry];
}

int PortPpuOverlayActive(void) {
    return sOverlay;
}

int PortPpuHudActive(void) {
    return sHudLayer;
}
uint32_t* gPortFrame;
uint32_t* gPortMenuBackground;

#define PLTT16 ((const uint16_t*)(uintptr_t)GBA_PLTT)
#define VRAM8 ((const uint8_t*)(uintptr_t)GBA_VRAM)
#define OAM16 ((const uint16_t*)(uintptr_t)GBA_OAM)

/* Line buffers hold BGR555 colours; bit 15 marks a transparent pixel. */
#define TRANSPARENT 0x8000

enum {
    LAYER_BG0,
    LAYER_BG1,
    LAYER_BG2,
    LAYER_BG3,
    LAYER_OBJ,
    LAYER_BD,
};

#define WIN_BG(n) (1 << (n))
#define WIN_OBJ 0x10
#define WIN_SFX 0x20

static uint16_t sBgLine[4][PORT_MAX_W];
static uint16_t sObjLine[PORT_MAX_W];
static int sLineHasObjects;
static uint8_t sObjPrio[PORT_MAX_W];
static uint8_t sObjIndex[PORT_MAX_W];
/* HUD layer: what covers each canvas pixel in the GBA's own compositing, so
   HUD sprites stay behind what the cartridge draws in front of them: the
   highest-priority opaque BG (4: none) and the winning other OBJ as
   priority * 128 + OAM index (0xFFFF: none). A window that hides OBJs there
   reads as 0 / 0. */
static uint8_t* sOccBg;
static uint8_t* sOccBgLayer;
/* HD-2D: 1 where a message window (docked layer) shows; allocated on use. */
static uint8_t* sMsgMask; /* 1 where a message window shows */
static uint16_t* sOccObj;
static uint8_t sObjSemi[PORT_MAX_W];
static uint8_t sObjWin[PORT_MAX_W];
static uint8_t sWinMask[PORT_MAX_W];
/* Wide view: 1 where some layer has world data (or inside the GBA picture);
   the backdrop shows black elsewhere, i.e. beyond the edge of the world. */
static uint8_t sInWorld[PORT_MAX_W];
static uint16_t sWorldPadding[4]; /* Opaque, uniform map-corner padding; never scenery repeated. */

/* Affine background reference points (internal registers). */
static int32_t sAffX[2], sAffY[2];
static uint32_t sAffLatchX[2], sAffLatchY[2];

static uint32_t sColorLut[0x8000];
static int sLutMode = -1;

/* Visible span of the current frame in GBA coordinates. */
static int sLeft, sRight, sTop, sBottom;

static int32_t Sext28(uint32_t v) {
    return (int32_t)(v << 4) >> 4;
}

static void BuildLut(void) {
    int c;

    if (sLutMode == gPortConfig.colorCorrection)
        return;
    sLutMode = gPortConfig.colorCorrection;
    for (c = 0; c < 0x8000; c++) {
        int r = c & 31, g = (c >> 5) & 31, b = (c >> 10) & 31;
        int R, G, B;

        if (sLutMode) {
            /* Approximation of the GBA's darker, desaturated LCD. */
            double lr = r / 31.0, lg = g / 31.0, lb = b / 31.0;
            double gr = lr * lr * 0.84 + lg * lg * 0.18 + lb * lb * 0.0;
            double gg = lr * lr * 0.09 + lg * lg * 0.67 + lb * lb * 0.26;
            double gb = lr * lr * 0.15 + lg * lg * 0.10 + lb * lb * 0.73;
            R = (int)(255.0 * (gr > 1 ? 1 : gr) + 0.5);
            G = (int)(255.0 * (gg > 1 ? 1 : gg) + 0.5);
            B = (int)(255.0 * (gb > 1 ? 1 : gb) + 0.5);
            /* gamma back up so the result is not overly dark */
            {
                R = (int)(sqrt(R / 255.0) * 255.0 + 0.5);
                G = (int)(sqrt(G / 255.0) * 255.0 + 0.5);
                B = (int)(sqrt(B / 255.0) * 255.0 + 0.5);
            }
        } else {
            R = (r << 3) | (r >> 2);
            G = (g << 3) | (g >> 2);
            B = (b << 3) | (b >> 2);
        }
        sColorLut[c] = 0xFF000000u | ((uint32_t)R << 16) | ((uint32_t)G << 8) | (uint32_t)B;
    }
}

void PortPpuSetResolution(int w, int h) {
    if (w > PORT_MAX_W)
        w = PORT_MAX_W;
    if (h > PORT_MAX_H)
        h = PORT_MAX_H;
    if (w < GBA_SCREEN_W)
        w = GBA_SCREEN_W;
    if (h < GBA_SCREEN_H)
        h = GBA_SCREEN_H;
    gPortScreen.width = w;
    gPortScreen.height = h;
    gPortScreen.originX = (w - GBA_SCREEN_W) / 2;
    gPortScreen.originY = (h - GBA_SCREEN_H) / 2;
    gPortViewLeft = -gPortScreen.originX;
    gPortViewTop = -gPortScreen.originY;
    gPortViewRight = w - gPortScreen.originX;
    gPortViewBottom = h - gPortScreen.originY;
    if (gPortFrame)
        PortCanvasAlloc();
}

/* Development aid (KHCOM_OAMDUMP): log the sprites of the current frame. */
void PortPpuDumpOam(void) {
    int i;

    for (i = 0; i < 128; i++) {
        uint16_t a0 = OAM16[i * 4], a1 = OAM16[i * 4 + 1], a2 = OAM16[i * 4 + 2];
        if ((a0 & 0x300) == 0x200)
            continue;
        PortLog("oam %3d ext(%4d,%4d) raw(%3d,%3d) shape %d size %d prio %d pal %2d tile %4d mode %d", i,
                sOamExt[i].x, sOamExt[i].y, a1 & 0x1FF, a0 & 0xFF, a0 >> 14, a1 >> 14, (a2 >> 10) & 3, a2 >> 12,
                a2 & 0x3FF, (a0 >> 10) & 3);
    }
}

void PortOamSetPosition(int index, int x, int y) {
    if (index >= 0 && index < 128) {
        sOamExt[index].x = (int16_t)x;
        sOamExt[index].y = (int16_t)y;
    }
}

void PortLatchBgMaps(const BgEntry* entries) {
    int b;

    for (b = 0; b < 4; b++) {
        BgLatch* l = &sBgLatch[b];
        l->map = entries[b].map;
        l->width = entries[b].width;
        l->height = entries[b].height;
        l->x = entries[b].x;
        l->y = entries[b].y;
        l->hofs = IO16(0x10 + b * 4) & 0x1FF;
        l->vofs = IO16(0x12 + b * 4) & 0x1FF;
        sBgShiftLatched[b] = sBgShift[b];
        sBgWorldLatched[b] = sBgWorld[b];
        sBgWorldLatched[b].hofs = l->hofs;
        sBgWorldLatched[b].vofs = l->vofs;
        sBgDockedLatched[b] = sBgDocked[b];
    }
}

void PortSetBattleArenaBands(int left, int right, int leftStart, int leftWidth,
                             int rightStart, int rightWidth) {
    if (left < 0 || right > 1024 || left >= right || leftWidth <= 0 || rightWidth <= 0 ||
        leftStart < left || leftStart + leftWidth > right ||
        rightStart < left || rightStart + rightWidth > right) {
        memset(sArenaBands, 0, sizeof(sArenaBands));
        return;
    }
    sArenaBands[0] = left; sArenaBands[1] = right;
    sArenaBands[2] = leftStart; sArenaBands[3] = leftWidth;
    sArenaBands[4] = rightStart; sArenaBands[5] = rightWidth;
}

static int ArenaBandPixel(int distance, int start, int width, int right) {
    int phase = distance % (width * 2);
    if (phase >= width) phase = width * 2 - 1 - phase;
    return start + (right ? width - 1 - phase : phase);
}

/* Battle: the card hand sits partly below the GBA screen; the sprites are
   whole, so the bottom HUD can be lifted to show more of them. */
static int HudRaise(void) {
    int r = gPortConfig.cardHudRaise;

    return !sBattleView || r < 0 ? 0 : (r > 16 ? 16 : r);
}

void PortSetBattleView(int on) {
    sBattleView = on;
    memset(sBgClip, 0, sizeof(sBgClip));
    memset(sArenaBands, 0, sizeof(sArenaBands));
}

/* Screen entry of the world map at world pixel (wx, wy); -1 outside it. */
static int WorldEntry(const BgLatch* l, int wx, int wy) {
    const uint16_t* block;

    /* battle stages continue sideways instead of ending in the void */
    if (sBattleView && l->width > 0 && (wx < 0 || wx >= l->width * 256))
        wx = ((wx % (l->width * 256)) + l->width * 256) % (l->width * 256);

    if (l->map == NULL || wx < 0 || wy < 0 || wx >= l->width * 256 || wy >= l->height * 256)
        return -1;
    block = (const uint16_t*)l->map[(wy >> 8) * l->width + (wx >> 8)];
    /* Blocks live in work RAM or the ROM; anything else is not a world map. */
    if ((uintptr_t)block < 0x02000000u || (uintptr_t)block >= 0x0A000000u)
        return -1;
    return block[((wy & 255) >> 3) * 32 + ((wx & 255) >> 3)];
}

/* Only a completely uniform, opaque corner tile is safe exterior padding.
 * Carry its palette colour beyond the map without stretching scenery or UI. */
static uint16_t WorldPadding(int bg, const BgLatch* l) {
    int corner, bpp8 = (IO16(8 + bg * 2) & 0x80) != 0;
    unsigned base = ((IO16(8 + bg * 2) >> 2) & 3) * 0x4000;
    if (!l->valid || sBgDockedLatched[bg] || sScreenBg[bg]) return TRANSPARENT;
    for (corner = 0; corner < 4; corner++) {
        int entry = WorldEntry(l, (corner & 1) ? l->width * 256 - 1 : 0,
                                  (corner & 2) ? l->height * 256 - 1 : 0);
        unsigned off; int ci, i, bytes = bpp8 ? 64 : 32;
        const uint8_t* tile;
        if (entry < 0) continue;
        off = base + (entry & 1023) * bytes;
        if (off + bytes > 0x10000) continue;
        tile = VRAM8 + off; ci = bpp8 ? tile[0] : tile[0] & 15;
        if (!ci || (!bpp8 && tile[0] != ci * 17)) continue;
        for (i = 1; i < bytes && tile[i] == tile[0]; i++) {}
        if (i == bytes) return PLTT16[(bpp8 ? 0 : (entry >> 12) * 16) + ci] & 0x7FFF;
    }
    return TRANSPARENT;
}

static int VramEntry(int bg, int gx, int gy) {
    uint16_t cnt = IO16(0x08 + bg * 2);
    const uint16_t* screen = (const uint16_t*)(VRAM8 + ((cnt >> 8) & 31) * 0x800);
    int size = cnt >> 14;
    int px = (gx + (IO16(0x10 + bg * 4) & 0x1FF)) & ((size & 1) ? 511 : 255);
    int py = (gy + (IO16(0x12 + bg * 4) & 0x1FF)) & ((size & 2) ? 511 : 255);
    int tx = px >> 3, ty = py >> 3, block = 0;

    if (tx >= 32)
        block += 1;
    if (ty >= 32)
        block += (size == 3) ? 2 : 1;
    return screen[block * 0x400 + (ty & 31) * 32 + (tx & 31)];
}

/* A map-block BG can be extended when what VRAM shows is the world map. */
static int ValidateBgLatch(int bg, uint16_t dispcnt) {
    static const int xs[3] = { 8, 120, 232 }, ys[3] = { 8, 80, 152 };
    BgLatch* l = &sBgLatch[bg];
    int mode = dispcnt & 7, i, j, match = 0;

    if (!(dispcnt & (0x100 << bg)) || l->map == NULL || l->width == 0 || l->height == 0)
        return 0;
    /* Message window layers are screen UI, never part of the world. */
    for (i = 0; i < 4; i++)
        if ((const void*)l->map == gMsgwinMapBlocks[i])
            return 0;
    if (mode > 1 || (mode == 1 && bg == 2))
        return 0;
    for (i = 0; i < 3; i++) {
        for (j = 0; j < 3; j++) {
            int we = WorldEntry(l, l->x + xs[i], l->y + ys[j]);
            if (we >= 0 && we == VramEntry(bg, xs[i], ys[j]))
                match++;
        }
    }
    return match >= 7;
}

/* Same check for a game-provided world (cell rooms). */
static int ValidateBgWorld(int bg, uint16_t dispcnt) {
    static const int xs[3] = { 8, 120, 232 }, ys[3] = { 8, 80, 152 };
    BgWorld* w = &sBgWorldLatched[bg];
    int mode = dispcnt & 7, i, j, match = 0;

    if (!(dispcnt & (0x100 << bg)) || w->fn == NULL || mode > 1 || (mode == 1 && bg == 2))
        return 0;
    for (i = 0; i < 3; i++)
        for (j = 0; j < 3; j++)
            if (w->fn(bg, (w->x + xs[i]) >> 3, (w->y + ys[j]) >> 3) == VramEntry(bg, xs[i], ys[j]))
                match++;
    return match >= 7;
}

/* ---- backgrounds --------------------------------------------------------- */

static void DrawTextBg(int bg, int gy, uint16_t dispcnt) {
    uint16_t cnt = IO16(0x08 + bg * 2);
    int hofs = IO16(0x10 + bg * 4) & 0x1FF;
    int vofs = IO16(0x12 + bg * 4) & 0x1FF;
    const uint8_t* chars = VRAM8 + ((cnt >> 2) & 3) * 0x4000;
    const uint16_t* screen = (const uint16_t*)(VRAM8 + ((cnt >> 8) & 31) * 0x800);
    int size = cnt >> 14;
    int wmask = (size & 1) ? 511 : 255;
    int hmask = (size & 2) ? 511 : 255;
    int bpp8 = (cnt >> 7) & 1;
    int mosaic = (cnt >> 6) & 1;
    int mosH = mosaic ? (IO16(0x4C) & 15) + 1 : 1;
    int mosV = mosaic ? ((IO16(0x4C) >> 4) & 15) + 1 : 1;
    uint16_t* out = sBgLine[bg];
    int x, py, ty, fy, outside;
    int w = gPortScreen.width;
    int cachedTx = 0, cachedTy = 0, cachedEntry = -1, cachedValid = 0;

    (void)dispcnt;
    if (mosV > 1)
        gy -= ((gy % mosV) + mosV) % mosV;
    py = (gy + vofs) & hmask;
    ty = py >> 3;
    fy = py & 7;
    outside = gy < 0 || gy >= GBA_SCREEN_H;
    if (sSpotlight && bg == 0) {
        /* Extend the authored shade, never the unused VRAM padding. */
        py = ((gy < 0 ? 0 : gy >= GBA_SCREEN_H ? GBA_SCREEN_H - 1 : gy) + vofs) & hmask;
        ty = py >> 3;
        fy = py & 7;
        outside = 0;
    }

    for (x = 0; x < w; x++) {
        int gx = x - gPortScreen.originX - sBgShiftLatched[bg];
        int px, tx, block, entry, tile, pal, fx, fyy, ci;
        const uint16_t* map;

        if (x - gPortScreen.originX < sLeft || x - gPortScreen.originX >= sRight) {
            out[x] = TRANSPARENT;
            continue;
        }
        if (sSpotlight && bg == 0)
            gx = (gx < 0 ? 0 : gx >= GBA_SCREEN_W ? GBA_SCREEN_W - 1 : gx);
        if (mosH > 1)
            gx -= ((gx % mosH) + mosH) % mosH;
        if ((outside || gx < 0 || gx >= GBA_SCREEN_W) && mosH == 1 &&
            !sScreenBg[bg] && !sBgDockedLatched[bg] &&
            (sBgLatch[bg].valid || sBgWorldLatched[bg].valid)) {
            const BgLatch* l = &sBgLatch[bg];
            const BgWorld* wd = &sBgWorldLatched[bg];
            int wx = l->valid ? l->x + gx + (hofs - l->hofs) : wd->x + gx + (hofs - wd->hofs);
            int wy = l->valid ? l->y + gy + (vofs - l->vofs) : wd->y + gy + (vofs - wd->vofs);
            int run = 8 - (wx & 7), we, j;
            if (run > w - x) run = w - x;
            if (run > sRight - (x - gPortScreen.originX)) run = sRight - (x - gPortScreen.originX);
            if (!outside && gx < 0 && run > -gx) run = -gx;
            we = l->valid ? WorldEntry(l, wx, wy) : wd->fn(bg, wx >> 3, wy >> 3);
            if (we < 0) {
                for (j = 0; j < run; j++) out[x + j] = sWorldPadding[bg];
                x += run - 1;
                continue;
            }
            /* World extensions sample one tile row at a time. UI glyphs
               keep the scalar path, including its exact registration order. */
            {
                unsigned base = ((cnt >> 2) & 3) * 0x4000;
                unsigned off = (we & 1023) * (bpp8 ? 64 : 32);
                if (bpp8 || !sHdText || base + off >= 0x10000 ||
                    sBgTextTiles[(base + off) / 32].code <= 0x20) {
                    int yy = (we & 0x800) ? 7 - (wy & 7) : wy & 7;
                    int palette = (we >> 12) * 16;
                    off += yy * (bpp8 ? 8 : 4);
                    memset(sInWorld + x, 1, run);
                    if (base + off + (bpp8 ? 8 : 4) > 0x10000) {
                        for (j = 0; j < run; j++) out[x + j] = TRANSPARENT;
                    } else {
                        int xx = (we & 0x400) ? 7 - (wx & 7) : wx & 7;
                        int step = (we & 0x400) ? -1 : 1;
                        const uint8_t* pixels = chars + off;
                        if (bpp8) {
                            for (j = 0; j < run; j++, xx += step) {
                                int c = pixels[xx];
                                out[x + j] = c ? PLTT16[c] & 0x7FFF : TRANSPARENT;
                            }
                        } else {
                            const uint16_t* colors = PLTT16 + palette;
                            for (j = 0; j < run; j++, xx += step) {
                                int c = (pixels[xx >> 1] >> ((xx & 1) * 4)) & 15;
                                out[x + j] = c ? colors[c] & 0x7FFF : TRANSPARENT;
                            }
                        }
                    }
                    x += run - 1;
                    continue;
                }
            }
        }
        if (outside || gx < 0 || gx >= GBA_SCREEN_W) {
            /* Beyond the hardware picture: only map-block layers continue. */
            const BgLatch* l = &sBgLatch[bg];
            int we;

            if (sScreenBg[bg] || sBgDockedLatched[bg] || (!l->valid && !sBgWorldLatched[bg].valid)) {
                out[x] = TRANSPARENT;
                continue;
            }
            if (!l->valid) {
                const BgWorld* wd = &sBgWorldLatched[bg];
                int wx = wd->x + gx + (hofs - wd->hofs), wy = wd->y + gy + (vofs - wd->vofs);
                /* Adjacent pixels share a map entry. Cache only this row,
                   so HBlank scroll/VRAM changes are never carried forward. */
                if (!cachedValid || cachedTx != (wx >> 3) || cachedTy != (wy >> 3)) {
                    cachedTx = wx >> 3; cachedTy = wy >> 3;
                    cachedEntry = wd->fn(bg, cachedTx, cachedTy);
                    cachedValid = 1;
                }
                we = cachedEntry;
                if (we < 0) {
                    out[x] = TRANSPARENT;
                    continue;
                }
                sInWorld[x] = 1;
                entry = we;
                px = wx & 7;
                fy = wy & 7;
                tile = entry & 0x3FF;
                fx = (entry & 0x400) ? 7 - px : px;
                fyy = (entry & 0x800) ? 7 - fy : fy;
                fy = py & 7;
                goto pixel;
            }
            {
                int wx = l->x + gx + (hofs - l->hofs), wy = l->y + gy + (vofs - l->vofs);
                if (!cachedValid || cachedTx != (wx >> 3) || cachedTy != (wy >> 3)) {
                    cachedTx = wx >> 3; cachedTy = wy >> 3;
                    cachedEntry = WorldEntry(l, wx, wy);
                    cachedValid = 1;
                }
                we = cachedEntry;
            }
            if (we < 0) {
                out[x] = sWorldPadding[bg];
                continue;
            }
            sInWorld[x] = 1;
            entry = we;
            px = (l->x + gx + (hofs - l->hofs)) & 7;
            fy = (l->y + gy + (vofs - l->vofs)) & 7;
            tile = entry & 0x3FF;
            fx = (entry & 0x400) ? 7 - px : px;
            fyy = (entry & 0x800) ? 7 - fy : fy;
            fy = py & 7;
            goto pixel;
        }
        px = (gx + hofs) & wmask;
        tx = px >> 3;
        block = 0;
        if (tx >= 32)
            block += 1;
        if (ty >= 32)
            block += (size == 3) ? 2 : 1;
        map = screen + block * 0x400;
        entry = map[(ty & 31) * 32 + (tx & 31)];
        tile = entry & 0x3FF;
        fx = (entry & 0x400) ? 7 - (px & 7) : (px & 7);
        fyy = (entry & 0x800) ? 7 - fy : fy;
    pixel:
        if (bpp8) {
            uint32_t off = tile * 64 + fyy * 8 + fx;
            ci = (((cnt >> 2) & 3) * 0x4000 + off < 0x10000) ? chars[off] : 0;
            out[x] = ci ? (PLTT16[ci] & 0x7FFF) : TRANSPARENT;
        } else {
            uint32_t off = tile * 32 + fyy * 4 + (fx >> 1);
            uint8_t b = (((cnt >> 2) & 3) * 0x4000 + off < 0x10000) ? chars[off] : 0;
            ci = (fx & 1) ? (b >> 4) : (b & 15);
            pal = entry >> 12;
            out[x] = ci ? (PLTT16[pal * 16 + ci] & 0x7FFF) : TRANSPARENT;
            if (sHdText && !(entry & 0xC00)) {
                unsigned offset = ((cnt >> 2) & 3) * 0x4000 + tile * 32;
                if (offset < 0x10000) {
                    const BgTextTile* text = &sBgTextTiles[offset / 32];
                    if (text->code > 0x20 && !memcmp(text->source, VRAM8 + offset, 32)) {
                        if ((px & 7) == 0 && ((py & 7) == 0 || gy == 0) && sBgTextCount < 1024) {
                            BgTextGlyph* glyph = &sBgTextGlyphs[sBgTextCount++];
                            int xx = x - (px & 7), yy = gy - (py & 7);
                            glyph->bg = (uint8_t)bg;
                            glyph->priority = cnt & 3;
                            glyph->screen = sOverlay && sScreenBg[bg];
                            if (glyph->screen) {
                                xx -= gPortScreen.originX;
                                if (sBgSplit[bg]) xx += xx < sBgSplit[bg] ? -PortScreenMarginX() : PortScreenMarginX();
                                xx += (gPortOverlayW - GBA_SCREEN_W) / 2;
                            } else yy += gPortScreen.originY;
                            memset(&glyph->glyph, 0, sizeof(glyph->glyph));
                            glyph->glyph.x = xx; glyph->glyph.y = yy;
                            glyph->glyph.code = text->code;
                            glyph->glyph.style = text->style;
                            glyph->glyph.cap = text->cap;
                            glyph->glyph.base = text->base;
                            /* Numeric BG cells use the same 13/14/15 panel,
                               shadow and face convention as EXP cells. */
                            {
                                /* the face is the lighter of the digit's two
                                   colours in this cell's palette (greyed-out
                                   panels use another palette) */
                                uint16_t a = PLTT16[pal * 16 + text->faceIndex] & 0x7FFF;
                                uint16_t b = PLTT16[pal * 16 + text->shadowIndex] & 0x7FFF;
                                int la = (a & 31) * 2 + ((a >> 5) & 31) * 5 + ((a >> 10) & 31);
                                int lb = (b & 31) * 2 + ((b >> 5) & 31) * 5 + ((b >> 10) & 31);
                                glyph->glyph.face = la >= lb ? a : b;
                                glyph->glyph.shadow = la >= lb ? b : a;
                            }
                        }
                        /* the pixel-art digit gives way to the panel colour, so
                           the layer keeps covering its cell and the occlusion
                           test still finds this panel in front */
                        if (ci == text->shadowIndex || ci == text->faceIndex)
                            out[x] = text->panelIndex ? (PLTT16[pal * 16 + text->panelIndex] & 0x7FFF) : TRANSPARENT;
                    }
                }
            }
        }
    }
}

/* Affine BG mosaic: the reference point of the first line of each block of
   mosV lines, which the following lines of the block reuse. */
static int32_t sMosAffX[2], sMosAffY[2];

/* Axis-aligned affine stages reuse their horizontal address calculation
   between scanlines. Cache coordinates only: VRAM and palette are still read
   on each line, so HBlank changes never reuse stale tile pixels or colours. */
static void DrawStraightAffine(int bg, int gy, uint16_t cnt, int32_t refX, int32_t refY) {
    static int keys[2][14], valid[2];
    static int16_t columns[2][PORT_MAX_W];
    int key[14], a = bg - 2, w = gPortScreen.width;
    int size = 128 << (cnt >> 14), tiles = size >> 3, wrap = (cnt >> 13) & 1;
    int py = refY >> 8, ornaments, x, i, lastTile = -1;
    uint16_t colors[8];
    uint16_t* out = sBgLine[bg];
    const uint8_t* chars = VRAM8 + ((cnt >> 2) & 3) * 0x4000;
    const uint8_t* screen = VRAM8 + ((cnt >> 8) & 31) * 0x800;

    if (sBattleView && gPortScreen.wide && ((cnt >> 2) & 3) == 0 &&
        ((cnt >> 8) & 31) == 12 && size >= 512 && gy >= GBA_SCREEN_H && py >= size)
        py = size - 1;
    ornaments = sBattleView && sArenaBands[1] && size >= 512 &&
                ((cnt >> 2) & 3) == 0 && ((cnt >> 8) & 31) == 12 && py >= 0 && py < size;
    if (wrap) py &= size - 1;
    else if (py < 0 || py >= size) {
        for (x = 0; x < w; x++) out[x] = TRANSPARENT;
        return;
    }
    key[0] = refX; key[1] = w; key[2] = gPortScreen.originX;
    key[3] = sLeft; key[4] = sRight; key[5] = cnt;
    key[6] = sBattleView; key[7] = ornaments;
    for (i = 0; i < 6; i++) key[8 + i] = sArenaBands[i];
    if (!valid[a] || memcmp(keys[a], key, sizeof(key))) {
        for (x = 0; x < w; x++) {
            int gx = x - gPortScreen.originX;
            int px = (refX + 256 * gx) >> 8;
            if (gx < sLeft || gx >= sRight) { columns[a][x] = -1; continue; }
            if (ornaments && (gx < 0 || gx >= GBA_SCREEN_W)) {
                if (px < sArenaBands[0])
                    px = ArenaBandPixel(sArenaBands[0] - 1 - px, sArenaBands[2], sArenaBands[3], 0);
                else if (px >= sArenaBands[1])
                    px = ArenaBandPixel(px - sArenaBands[1], sArenaBands[4], sArenaBands[5], 1);
            }
            if (wrap || ((px < 0 || px >= size) && size >= 512 && (gx < 0 || gx >= GBA_SCREEN_W)))
                px &= size - 1;
            columns[a][x] = (px >= 0 && px < size) ? (int16_t)px : -1;
        }
        memcpy(keys[a], key, sizeof(key)); valid[a] = 1;
    }
    screen += (py >> 3) * tiles;
    for (x = 0; x < w; x++) {
        int px = columns[a][x], tile;
        if (px < 0) { out[x] = TRANSPARENT; continue; }
        sInWorld[x] = 1;
        tile = screen[px >> 3];
        if (tile != lastTile) {
            const uint8_t* pixels = chars + tile * 64 + (py & 7) * 8;
            for (i = 0; i < 8; i++) colors[i] = pixels[i] ? PLTT16[pixels[i]] & 0x7FFF : TRANSPARENT;
            lastTile = tile;
        }
        out[x] = colors[px & 7];
    }
}

static void DrawAffineBg(int bg, int gy, uint16_t dispcnt) {
    int a = bg - 2;
    uint16_t cnt = IO16(0x08 + bg * 2);
    int16_t pa = (int16_t)IO16(0x20 + a * 0x10);
    int16_t pc = (int16_t)IO16(0x24 + a * 0x10);
    const uint8_t* chars = VRAM8 + ((cnt >> 2) & 3) * 0x4000;
    const uint8_t* screen = VRAM8 + ((cnt >> 8) & 31) * 0x800;
    int size = 128 << (cnt >> 14);
    int tiles = size >> 3;
    int wrap = (cnt >> 13) & 1;
    uint16_t* out = sBgLine[bg];
    int x, w = gPortScreen.width;
    int mosaic = (cnt >> 6) & 1;
    int mosH = mosaic ? (IO16(0x4C) & 15) + 1 : 1;
    int mosV = mosaic ? ((IO16(0x4C) >> 4) & 15) + 1 : 1;
    int32_t refX = sAffX[a], refY = sAffY[a];
    int32_t rx, ry;

    (void)dispcnt;
    if (mosV > 1) {
        if (((gy % mosV) + mosV) % mosV == 0) {
            sMosAffX[a] = refX;
            sMosAffY[a] = refY;
        }
        refX = sMosAffX[a];
        refY = sMosAffY[a];
    }
    if (pa == 256 && pc == 0 && mosH == 1) {
        DrawStraightAffine(bg, gy, cnt, refX, refY);
        return;
    }
    rx = refX + (int32_t)pa * (-gPortScreen.originX);
    ry = refY + (int32_t)pc * (-gPortScreen.originX);
    for (x = 0; x < w; x++, rx += pa, ry += pc) {
        int gx = x - gPortScreen.originX;
        int px, py;
        int tile, ci;

        if (mosH > 1) { /* every block of mosH pixels shows its first one */
            int gq = gx - ((gx % mosH) + mosH) % mosH;
            px = (refX + (int32_t)pa * gq) >> 8;
            py = (refY + (int32_t)pc * gq) >> 8;
        } else {
            px = rx >> 8;
            py = ry >> 8;
        }

        if (gx < sLeft || gx >= sRight) {
            out[x] = TRANSPARENT;
            continue;
        }
        /* Outside the original picture, continue the bottom of the arena
           in texture space. Composition still handles palette zero, fades,
           masks and sprites normally; no framebuffer colours are guessed. */
        if (sBattleView && gPortScreen.wide && ((cnt >> 2) & 3) == 0 && ((cnt >> 8) & 31) == 12 && size >= 512 &&
            gy >= GBA_SCREEN_H && py >= size)
            py = size - 1;
        /* Continue authored arena ornaments only in the wide margins. The
           original hardware viewport, camera and collision remain exact.
           Reflecting each short side band joins its edge without bringing
           padding or unique centre landmarks into the added view. */
        if (sBattleView && sArenaBands[1] && size >= 512 &&
            ((cnt >> 2) & 3) == 0 && ((cnt >> 8) & 31) == 12 &&
            (gx < 0 || gx >= GBA_SCREEN_W) && py >= 0 && py < size) {
            if (px < sArenaBands[0])
                px = ArenaBandPixel(sArenaBands[0] - 1 - px,
                                    sArenaBands[2], sArenaBands[3], 0);
            else if (px >= sArenaBands[1])
                px = ArenaBandPixel(px - sArenaBands[1],
                                    sArenaBands[4], sArenaBands[5], 1);
        }
        if (wrap) {
            px &= size - 1;
            py &= size - 1;
        } else if ((px < 0 || px >= size) && py >= 0 && py < size && size >= 512 && (gx < 0 || gx >= GBA_SCREEN_W)) {
            /* wide margins of a battle arena: the stage repeats sideways
               instead of ending in the void */
            px &= size - 1;
        } else if (px < 0 || py < 0 || px >= size || py >= size) {
            out[x] = TRANSPARENT;
            continue;
        }
        sInWorld[x] = 1;
        tile = screen[(py >> 3) * tiles + (px >> 3)];
        ci = chars[tile * 64 + (py & 7) * 8 + (px & 7)];
        out[x] = ci ? (PLTT16[ci] & 0x7FFF) : TRANSPARENT;
    }
}

static void DrawBitmapBg(int mode, int gy, uint16_t dispcnt) {
    int16_t pa = (int16_t)IO16(0x20);
    int16_t pc = (int16_t)IO16(0x24);
    uint16_t* out = sBgLine[2];
    int x, w = gPortScreen.width;
    int bw = (mode == 5) ? 160 : 240;
    int bh = (mode == 5) ? 128 : 160;
    uint32_t page = (mode != 3 && (dispcnt & 0x10)) ? 0xA000 : 0;
    int mosaic = (IO16(0x0C) >> 6) & 1;
    int mosH = mosaic ? (IO16(0x4C) & 15) + 1 : 1;
    int mosV = mosaic ? ((IO16(0x4C) >> 4) & 15) + 1 : 1;
    int32_t refX = sAffX[0], refY = sAffY[0], rx, ry;

    /* Bitmap modes use BG2's affine engine, including its screen-space
       mosaic. Reuse the first line's reference point within each block. */
    if (mosV > 1) {
        if (((gy % mosV) + mosV) % mosV == 0) {
            sMosAffX[0] = refX;
            sMosAffY[0] = refY;
        }
        refX = sMosAffX[0];
        refY = sMosAffY[0];
    }
    rx = refX + (int32_t)pa * (-gPortScreen.originX);
    ry = refY + (int32_t)pc * (-gPortScreen.originX);

    for (x = 0; x < w; x++, rx += pa, ry += pc) {
        int gx = x - gPortScreen.originX;
        int px = rx >> 8, py = ry >> 8;

        if (mosH > 1) {
            int first = gx - ((gx % mosH) + mosH) % mosH;
            px = (refX + (int32_t)pa * first) >> 8;
            py = (refY + (int32_t)pc * first) >> 8;
        }

        if (gx < sLeft || gx >= sRight || px < 0 || py < 0 || px >= bw || py >= bh) {
            out[x] = TRANSPARENT;
            continue;
        }
        if (mode == 4) {
            int ci = VRAM8[page + py * 240 + px];
            out[x] = ci ? (PLTT16[ci] & 0x7FFF) : TRANSPARENT;
        } else {
            out[x] = *(const uint16_t*)(VRAM8 + page + (py * bw + px) * 2) & 0x7FFF;
        }
    }
}

/* ---- sprites --------------------------------------------------------------- */

static const uint8_t sObjSize[3][4][2] = {
    { { 8, 8 }, { 16, 16 }, { 32, 32 }, { 64, 64 } },
    { { 16, 8 }, { 32, 8 }, { 32, 16 }, { 64, 32 } },
    { { 8, 16 }, { 8, 32 }, { 16, 32 }, { 32, 64 } },
};

static void DrawObjs(int gy, uint16_t dispcnt) {
    int i, w = gPortScreen.width;
    int mapping1d = (dispcnt >> 6) & 1;
    int bitmapMode = (dispcnt & 7) >= 3;
    uint16_t mosaic = IO16(0x4C);
    int mosH = ((mosaic >> 8) & 15) + 1;
    int mosV = ((mosaic >> 12) & 15) + 1;

    sLineHasObjects = 0;
    for (i = 0; i < w; i++) {
        sObjLine[i] = TRANSPARENT;
        sObjPrio[i] = 4;
        sObjSemi[i] = 0;
        sScrLine[i] = TRANSPARENT;
        sScrPrio[i] = 4;
        sScrIndex[i] = 127;
        sObjWin[i] = 0;
    }
    if (!(dispcnt & 0x1000))
        return;

    for (i = 0; i < 128; i++) {
        uint16_t a0 = OAM16[i * 4 + 0];
        uint16_t a1 = OAM16[i * 4 + 1];
        uint16_t a2 = OAM16[i * 4 + 2];
        int affine = (a0 >> 8) & 1;
        int dbl = (a0 >> 9) & 1;
        int mode = (a0 >> 10) & 3;
        int shape = (a0 >> 14) & 3;
        int size = (a1 >> 14) & 3;
        int ow, oh, bw, bh, ox, oy, line, sx, x;
        int bpp8 = (a0 >> 13) & 1;
        int prio = (a2 >> 10) & 3;
        int tileBase = a2 & 0x3FF;
        int palBank = a2 >> 12;
        int16_t pa = 0x100, pb = 0, pc = 0, pd = 0x100;
        int objMosaic = (a0 >> 12) & 1;

        if (!affine && dbl)
            continue; /* disabled */
        if (shape == 3 || mode == 3)
            continue;
        if (sHudLayer && sOamTag[i].hud)
            continue; /* drawn by PortPpuRenderHud */
        if (HdTextGlyph(i) && sOamTag[i].style != 2)
            continue; /* drawn by port_hdtext.c */
        ow = sObjSize[shape][size][0];
        oh = sObjSize[shape][size][1];
        bw = ow << (affine && dbl);
        bh = oh << (affine && dbl);

        /* Decode the 8-bit Y and 9-bit X against the visible span. */
        oy = a0 & 0xFF;
        ox = a1 & 0x1FF;
        if ((sOamExt[i].x & 0x1FF) == ox && (sOamExt[i].y & 0xFF) == oy) {
            ox = sOamExt[i].x;
            oy = sOamExt[i].y;
        } else {
            if (oy >= sBottom)
                oy -= 256;
            if (ox >= sRight)
                ox -= 512;
        }
        if (ox >= sRight || ox + bw <= sLeft)
            continue;

        line = gy - oy;
        /* Reject lines outside the sprite before mosaic quantisation:
           truncating a negative remainder would turn -1 into line zero. */
        if (line < 0 || line >= bh)
            continue;
        if (objMosaic && mosV > 1)
            line -= line % mosV;
        if (bitmapMode && tileBase < 512)
            continue;

        if (affine) {
            const uint16_t* p = OAM16 + ((a1 >> 9) & 31) * 16;
            pa = (int16_t)p[3];
            pb = (int16_t)p[7];
            pc = (int16_t)p[11];
            pd = (int16_t)p[15];
        }

        for (sx = 0; sx < bw; sx++) {
            int gx = ox + sx;
            int fx = gx;
            int tx, ty, tile, ci, col;
            uint32_t off;

            if (gx < sLeft || gx >= sRight)
                continue;
            x = gx + gPortScreen.originX;
            if (x < 0 || x >= w)
                continue;
            if (objMosaic && mosH > 1)
                fx = gx - (((gx % mosH) + mosH) % mosH);
            fx -= ox;

            if (affine) {
                int cx = fx - bw / 2, cy = line - bh / 2;
                tx = ((pa * cx + pb * cy) >> 8) + ow / 2;
                ty = ((pc * cx + pd * cy) >> 8) + oh / 2;
                if (tx < 0 || ty < 0 || tx >= ow || ty >= oh)
                    continue;
            } else {
                if (fx < 0 || fx >= ow)
                    continue;
                tx = (a1 & 0x1000) ? ow - 1 - fx : fx;
                ty = (a1 & 0x2000) ? oh - 1 - line : line;
            }

            if (bpp8) {
                if (mapping1d)
                    tile = tileBase + ((ty >> 3) * (ow >> 3) + (tx >> 3)) * 2;
                else
                    tile = tileBase + (ty >> 3) * 32 + (tx >> 3) * 2;
                off = 0x10000 + (tile & 0x3FF) * 32 + (ty & 7) * 8 + (tx & 7);
                ci = VRAM8[off];
                col = ci ? (PLTT16[256 + ci] & 0x7FFF) : -1;
            } else {
                if (mapping1d)
                    tile = tileBase + (ty >> 3) * (ow >> 3) + (tx >> 3);
                else
                    tile = tileBase + (ty >> 3) * 32 + (tx >> 3);
                off = 0x10000 + (tile & 0x3FF) * 32 + (ty & 7) * 4 + ((tx & 7) >> 1);
                ci = (tx & 1) ? (VRAM8[off] >> 4) : (VRAM8[off] & 15);
                col = ci ? (PLTT16[256 + palBank * 16 + ci] & 0x7FFF) : -1;
            }
            if (col < 0)
                continue;
            if (sOamTag[i].header && x < gPortScreen.originX) {
                /* off the GBA screen: the band, not hidden lettering */
                int band = HeaderBandColor(gy, x - gPortScreen.originX); /* headers are drawn at y 0 */
                if (band >= 0)
                    col = band;
            }
            if (HdTextGlyph(i) && sOamTag[i].style == 2 && (ci == 14 || ci == 15))
                col = PLTT16[256 + palBank * 16 + 13] & 0x7FFF; /* Refill old ink with the blue panel, not transparency. */
            if (mode == 2) {
                sObjWin[x] = 1;
                continue;
            }
            if (sOverlay && sOamTag[i].screen) {
                if (sScrLine[x] == TRANSPARENT || prio < sScrPrio[x]) {
                    sScrLine[x] = (uint16_t)col;
                    sScrPrio[x] = (uint8_t)prio;
                    sScrIndex[x] = (uint8_t)i;
                    sScrSemi[x] = (mode == 1);
                }
            } else if (sObjLine[x] == TRANSPARENT || prio < sObjPrio[x]) {
                sLineHasObjects = 1;
                sObjLine[x] = (uint16_t)col;
                sObjPrio[x] = (uint8_t)prio;
                sObjIndex[x] = (uint8_t)i;
                sObjSemi[x] = (mode == 1);
            }
        }
    }
}

/* ---- windows --------------------------------------------------------------- */

static void WinSpan(uint16_t reg, int limit, int lo, int hi, int* a, int* b, int* wrapped) {
    int s = reg >> 8, e = reg & 0xFF;

    *wrapped = 0;
    if (e > limit || s > e) {
        if (s > e && e <= limit) {
            *wrapped = 1; /* covers [s, limit) and [0, e) */
        } else {
            e = limit;
        }
    }
    /* A window spanning the whole original screen spans the wide view too. */
    if (!*wrapped && s == 0 && e >= limit) {
        s = lo;
        e = hi;
    }
    *a = s;
    *b = e;
}

static int InWin(int v, int a, int b, int wrapped, int limit, int lo, int hi) {
    if (wrapped)
        return (v >= a && v < hi) || (v < b && v >= lo) || (a >= limit && v >= limit);
    return v >= a && v < b;
}

static void BuildWindows(int gy, uint16_t dispcnt) {
    int w = gPortScreen.width;
    int x;
    uint16_t winin = IO16(0x48), winout = IO16(0x4A);
    int win0 = (dispcnt >> 13) & 1, win1 = (dispcnt >> 14) & 1, winObj = (dispcnt >> 15) & 1;
    int in0 = 0, in1 = 0;
    int a0 = 0, b0 = 0, w0 = 0, a1 = 0, b1 = 0, w1 = 0;

    if (!win0 && !win1 && !winObj) {
        memset(sWinMask, 0x3F, w);
        return;
    }
    if (win0) {
        int ya, yb, yw;
        WinSpan(IO16(0x44), GBA_SCREEN_H, sTop, sBottom, &ya, &yb, &yw);
        in0 = InWin(gy, ya, yb, yw, GBA_SCREEN_H, sTop, sBottom);
        WinSpan(IO16(0x40), GBA_SCREEN_W, sLeft, sRight, &a0, &b0, &w0);
    }
    if (win1) {
        int ya, yb, yw;
        WinSpan(IO16(0x46), GBA_SCREEN_H, sTop, sBottom, &ya, &yb, &yw);
        in1 = InWin(gy, ya, yb, yw, GBA_SCREEN_H, sTop, sBottom);
        WinSpan(IO16(0x42), GBA_SCREEN_W, sLeft, sRight, &a1, &b1, &w1);
    }
    for (x = 0; x < w; x++) {
        int gx = x - gPortScreen.originX;
        uint8_t m = winout & 0x3F;

        if (winObj && sObjWin[x])
            m = (winout >> 8) & 0x3F;
        if (in1 && InWin(gx, a1, b1, w1, GBA_SCREEN_W, sLeft, sRight))
            m = (winin >> 8) & 0x3F;
        if (in0 && InWin(gx, a0, b0, w0, GBA_SCREEN_W, sLeft, sRight))
            m = winin & 0x3F;
        sWinMask[x] = m;
    }
}

/* ---- composition ----------------------------------------------------------- */

static uint16_t Blend(uint16_t a, uint16_t b, int ea, int eb) {
    int r = ((a & 31) * ea + (b & 31) * eb) >> 4;
    int g = (((a >> 5) & 31) * ea + ((b >> 5) & 31) * eb) >> 4;
    int bl = (((a >> 10) & 31) * ea + ((b >> 10) & 31) * eb) >> 4;

    if (r > 31)
        r = 31;
    if (g > 31)
        g = 31;
    if (bl > 31)
        bl = 31;
    return (uint16_t)(r | (g << 5) | (bl << 10));
}

static uint16_t Brighten(uint16_t c, int ey) {
    int r = c & 31, g = (c >> 5) & 31, b = (c >> 10) & 31;

    r += ((31 - r) * ey) >> 4;
    g += ((31 - g) * ey) >> 4;
    b += ((31 - b) * ey) >> 4;
    return (uint16_t)(r | (g << 5) | (b << 10));
}

static uint16_t Darken(uint16_t c, int ey) {
    int r = c & 31, g = (c >> 5) & 31, b = (c >> 10) & 31;

    r -= (r * ey) >> 4;
    g -= (g * ey) >> 4;
    b -= (b * ey) >> 4;
    return (uint16_t)(r | (g << 5) | (b << 10));
}

static void BuildNarrowSides(int gy, uint16_t dispcnt, const int* bgOn, const int* bgPrio);

static void ComposeLine(int y, uint16_t dispcnt, const int* bgOn, const int* bgPrio, uint32_t* frame, int objects) {
    int w = gPortScreen.width;
    uint32_t* dst = frame + y * w;
    uint16_t bldcnt = IO16(0x50), bldalpha = IO16(0x52);
    int eva = bldalpha & 31, evb = (bldalpha >> 8) & 31;
    int evy = IO16(0x54) & 31, effect = (bldcnt >> 6) & 3;
    uint16_t backdrop = PLTT16[0] & 0x7FFF;
    int order[4], n = 0, p, b, x, docked = 0;
    int collect = objects && (sHudLayer || sHdText || PortHd2dActive());
    int row = y * w;

    if (eva > 16) eva = 16;
    if (evb > 16) evb = 16;
    if (evy > 16) evy = 16;
    for (p = 0; p < 4; p++)
        for (b = 0; b < 4; b++)
            if (bgOn[b] && !sScreenBg[b] && bgPrio[b] == p)
                order[n++] = b;
    if (collect)
        for (b = 0; b < 4; b++)
            if (bgOn[b] && sBgDockedLatched[b]) docked |= 1 << b;

    /* Most extra world scanlines contain only opaque backgrounds. Windows,
       object alpha, docked messages and colour effects retain the full path.
       Keep priority metadata identical for HUD and HD text consumers. */
    if (gPortScreen.wide && !(dispcnt & 0xE000) &&
        (!objects || !sLineHasObjects) && !docked &&
        (effect == 0 || !(bldcnt & 0x3F)) &&
        !(sSpotlight && (sScreenBgMask & 2u))) {
        for (x = 0; x < w; x++) {
            int bg = -1;
            for (b = 0; b < n; b++) {
                int candidate = order[b];
                if (sBgLine[candidate][x] != TRANSPARENT) { bg = candidate; break; }
            }
            dst[x] = sColorLut[bg < 0 ? (sInWorld[x] ? backdrop : 0) : sBgLine[bg][x]];
            if (collect) {
                sMsgMask[row + x] = 0;
                sOccBg[row + x] = bg < 0 ? 4 : (uint8_t)bgPrio[bg];
                sOccBgLayer[row + x] = bg < 0 ? 4 : (uint8_t)bg;
                sOccObj[row + x] = 0xFFFFu;
            }
        }
        return;
    }

    for (x = 0; x < w; x++) {
        int gx = x - gPortScreen.originX;
        uint8_t mask = sWinMask[x];
        uint16_t bd = sInWorld[x] ? backdrop : 0;
        uint16_t top, second = bd, col;
        int first, topLayer, secondLayer = LAYER_BD, bg = -1;
        int obj = objects && (mask & WIN_OBJ) && sObjLine[x] != TRANSPARENT;
        int objFront, blend;

        if (gx < sLeft || gx >= sRight ||
            (sSpotlight && (gx < 0 || gx >= GBA_SCREEN_W || y < gPortScreen.originY ||
                           y >= gPortScreen.originY + GBA_SCREEN_H))) {
            dst[x] = 0xFF000000u;
            continue;
        }
        /* Find the first visible BG once. Composition and HD occlusion use
           the same priority decision; the second layer is needed only for
           alpha, not for opaque pixels or brightness effects. */
        for (first = 0; first < n; first++) {
            b = order[first];
            if ((mask & WIN_BG(b)) && sBgLine[b][x] != TRANSPARENT) {
                bg = b;
                break;
            }
        }
        if (collect) {
            int message = 0;
            if (docked)
                for (b = 0; b < 4; b++)
                    if ((docked & (1 << b)) && (mask & WIN_BG(b)) && sBgLine[b][x] != TRANSPARENT)
                        message = 1;
            sMsgMask[row + x] = (uint8_t)message;
            if (!(mask & WIN_OBJ) || (message && sHudLayer)) {
                sOccBg[row + x] = sOccBgLayer[row + x] = 0;
                sOccObj[row + x] = 0;
            } else {
                sOccBg[row + x] = bg < 0 ? 4 : (uint8_t)bgPrio[bg];
                sOccBgLayer[row + x] = bg < 0 ? 4 : (uint8_t)bg;
                sOccObj[row + x] = sObjLine[x] != TRANSPARENT ?
                    (uint16_t)(sObjPrio[x] * 128 + sObjIndex[x]) : 0xFFFFu;
            }
        }
        objFront = obj && (bg < 0 || sObjPrio[x] <= bgPrio[bg]);
        topLayer = objFront ? LAYER_OBJ : bg < 0 ? LAYER_BD : bg;
        top = objFront ? sObjLine[x] : bg < 0 ? bd : sBgLine[bg][x];
        blend = (objFront && sObjSemi[x]) ||
                ((mask & WIN_SFX) && effect == 1 && (bldcnt & (1 << topLayer)));
        if (blend) {
            if (objFront) {
                if (bg >= 0) { second = sBgLine[bg][x]; secondLayer = bg; }
            } else if (bg >= 0) {
                int next = -1;
                for (b = first + 1; b < n; b++) {
                    int k = order[b];
                    if ((mask & WIN_BG(k)) && sBgLine[k][x] != TRANSPARENT) { next = k; break; }
                }
                if (obj && (next < 0 || sObjPrio[x] <= bgPrio[next])) {
                    second = sObjLine[x]; secondLayer = LAYER_OBJ;
                } else if (next >= 0) {
                    second = sBgLine[next][x]; secondLayer = next;
                }
            }
        }
        col = top;
        if (objFront && sObjSemi[x] && (bldcnt & (0x100 << secondLayer))) {
            col = Blend(top, second, eva, evb);
        } else if ((mask & WIN_SFX) && (bldcnt & (1 << topLayer))) {
            switch (effect) {
                case 1:
                    if (bldcnt & (0x100 << secondLayer)) col = Blend(top, second, eva, evb);
                    break;
                case 2: col = Brighten(top, evy); break;
                case 3: col = Darken(top, evy); break;
            }
        }
        dst[x] = sColorLut[col];
    }
}

/* ---- frame ------------------------------------------------------------------ */

static void LatchAffine(int force) {
    int a;

    for (a = 0; a < 2; a++) {
        uint32_t rx = IO32(0x28 + a * 0x10), ry = IO32(0x2C + a * 0x10);
        if (force || rx != sAffLatchX[a]) {
            sAffLatchX[a] = rx;
            sAffX[a] = Sext28(rx);
        }
        if (force || ry != sAffLatchY[a]) {
            sAffLatchY[a] = ry;
            sAffY[a] = Sext28(ry);
        }
    }
}

static void StepAffine(int lines) {
    int a;

    for (a = 0; a < 2; a++) {
        sAffX[a] += (int16_t)IO16(0x22 + a * 0x10) * lines;
        sAffY[a] += (int16_t)IO16(0x26 + a * 0x10) * lines;
    }
}

void PortBgClip(int bg, int on) {
    if ((unsigned)bg < 4) sBgClip[bg] = on;
}

void PortBgSplitBands(int bg, int enabled) {
    if ((unsigned)bg < 4) sBgSplitBands[bg] = enabled;
}

static void SplitBgLine(int b, int gy) {
    static uint16_t tmp[PORT_MAX_W];
    int w = gPortScreen.width, m = PortScreenMarginX(), split = sBgSplit[b], x;

    memcpy(tmp, sBgLine[b], (size_t)w * 2);
    for (x = 0; x < w; x++) {
        int gx = x - gPortScreen.originX, c;
        if (gx < split - m)
            c = gx + m;
        else if (gx >= split + m)
            c = gx - m;
        else {
            if (sBgSplitBands[b] && (gy < 8 || gy >= 152)) {
                /* Repeat the outermost complete tile of the stat-side band.
                   This excludes OBJ cursors, text and the battle backdrop. */
                c = gPortScreen.originX + GBA_SCREEN_W - 8 + ((gx - split + m) & 7);
                sBgLine[b][x] = (c >= 0 && c < w) ? tmp[c] : TRANSPARENT;
                continue;
            }
            sBgLine[b][x] = TRANSPARENT;
            continue;
        }
        c += gPortScreen.originX;
        sBgLine[b][x] = (c >= 0 && c < w) ? tmp[c] : TRANSPARENT;
    }
}

/* The screen layer's line gy: menu layers only, transparent elsewhere. */
static void ComposeOverlayLine(int gy, uint16_t dispcnt, const int* bgOn, const int* bgPrio) {
    int wo = gPortOverlayW, w = gPortScreen.width;
    int originO = (wo - GBA_SCREEN_W) / 2;
    uint32_t* dst = gPortOverlay + gy * wo;
    uint16_t bldcnt = IO16(0x50), bldalpha = IO16(0x52);
    int eva = ((bldalpha & 31) > 16 ? 16 : (bldalpha & 31)), evb = (((bldalpha >> 8) & 31) > 16 ? 16 : ((bldalpha >> 8) & 31));
    int evy = ((IO16(0x54) & 31) > 16 ? 16 : (IO16(0x54) & 31)), effect = (bldcnt >> 6) & 3;
    int order[4], n = 0, p, b, ox;

    for (p = 0; p < 4; p++)
        for (b = 0; b < 4; b++)
            if (bgOn[b] && sScreenBg[b] && bgPrio[b] == p)
                order[n++] = b;
    for (ox = 0; ox < wo; ox++) {
        int gx = ox - originO, x = gx + gPortScreen.originX, i, found = 0, objDone = 0;
        int topLayer = LAYER_BD, secondLayer = LAYER_BD;
        uint16_t top = 0, second = 0, col;
        uint8_t mask;

        dst[ox] = 0;
        sScreenOccBg[gy * wo + ox] = 0;
        sScreenOccBgLayer[gy * wo + ox] = 0;
        sScreenOccObj[gy * wo + ox] = 0;
        if (x < 0 || x >= w || gx < sLeft || gx >= sRight)
            continue;
        mask = sWinMask[x];
        if (sHdText && (mask & WIN_OBJ)) {
            int occ = 4, occLayer = 4;
            for (i = 0; i < n; i++) {
                if ((mask & WIN_BG(order[i])) && sBgLine[order[i]][x] != TRANSPARENT) {
                    occ = bgPrio[order[i]];
                    occLayer = order[i];
                    break;
                }
            }
            sScreenOccBg[gy * wo + ox] = (uint8_t)occ;
            sScreenOccBgLayer[gy * wo + ox] = (uint8_t)occLayer;
            sScreenOccObj[gy * wo + ox] = sScrLine[x] != TRANSPARENT ?
                (uint16_t)(sScrPrio[x] * 128 + sScrIndex[x]) : 0xFFFF;
        }
        for (i = 0; i <= n && found < 2; i++) {
            int prio = (i < n) ? bgPrio[order[i]] : 4;
            if (!objDone && (mask & WIN_OBJ) && sScrLine[x] != TRANSPARENT && sScrPrio[x] <= prio) {
                objDone = 1;
                if (found++ == 0) {
                    top = sScrLine[x];
                    topLayer = LAYER_OBJ;
                } else {
                    second = sScrLine[x];
                    secondLayer = LAYER_OBJ;
                }
                if (found == 2)
                    break;
            }
            if (i < n && (mask & WIN_BG(order[i])) && sBgLine[order[i]][x] != TRANSPARENT) {
                if (found++ == 0) {
                    top = sBgLine[order[i]][x];
                    topLayer = order[i];
                } else {
                    second = sBgLine[order[i]][x];
                    secondLayer = order[i];
                }
            }
        }
        if (found == 0)
            continue;
        col = top;
        {
            uint32_t alpha = 0xFF000000u;
            int blend = (topLayer == LAYER_OBJ && sScrSemi[x]) || ((mask & WIN_SFX) && effect == 1 && (bldcnt & (1 << topLayer)));
            if (blend) {
                if (found == 2 && (bldcnt & (0x100 << secondLayer)))
                    col = Blend(top, second, eva, evb);
                else
                    alpha = (uint32_t)(eva * 16 > 255 ? 255 : eva * 16) << 24; /* over the world below */
            } else if ((mask & WIN_SFX) && (bldcnt & (1 << topLayer))) {
                if (effect == 2)
                    col = Brighten(top, evy);
                else if (effect == 3)
                    col = Darken(top, evy);
            }
            dst[ox] = (sColorLut[col] & 0x00FFFFFFu) | alpha;
        }
    }
}

static void RenderLine(int y, int gy) {
    uint16_t dispcnt = IO16(0x00);
    int mode = dispcnt & 7;
    int bgOn[4] = { 0, 0, 0, 0 }, bgPrio[4];
    int b, w = gPortScreen.width;

    if (dispcnt & 0x80) {
        uint32_t* dst = gPortFrame + y * w;
        int x;
        for (x = 0; x < w; x++) {
            int gx = x - gPortScreen.originX;
            dst[x] = (gx < sLeft || gx >= sRight) ? 0xFF000000u : 0xFFFFFFFFu;
            gPortMenuBackground[y * w + x] = dst[x];
        }
        return;
    }

    {
        int x, inside = !gPortScreen.wide || (gy >= 0 && gy < GBA_SCREEN_H);
        for (x = 0; x < w; x++) {
            int gx = x - gPortScreen.originX;
            sInWorld[x] = inside && (!gPortScreen.wide || (gx >= 0 && gx < GBA_SCREEN_W));
        }
    }

    for (b = 0; b < 4; b++) {
        bgPrio[b] = IO16(0x08 + b * 2) & 3;
        if (!(dispcnt & (0x100 << b)))
            continue;
        switch (mode) {
            case 0:
                bgOn[b] = 1;
                break;
            case 1:
                bgOn[b] = b <= 2;
                break;
            case 2:
                bgOn[b] = b >= 2;
                break;
            default:
                bgOn[b] = b == 2;
                break;
        }
    }

    for (b = 0; b < 4; b++) {
        if (!bgOn[b])
            continue;
        if (mode >= 3)
            DrawBitmapBg(mode, gy, dispcnt);
        else if (b >= 2 && (mode == 2 || (mode == 1 && b == 2)))
            DrawAffineBg(b, gy, dispcnt);
        else
            DrawTextBg(b, gy, dispcnt);
        if (sOverlay && sScreenBg[b] && sBgSplit[b])
            SplitBgLine(b, gy);
        else if (sBgClip[b] && !(sOverlay && sScreenBg[b])) {
            /* its wrapped columns would show in the margins */
            int x;
            for (x = 0; x < w; x++)
                if (x - gPortScreen.originX < 0 || x - gPortScreen.originX >= GBA_SCREEN_W)
                    sBgLine[b][x] = TRANSPARENT;
        }
    }
    DrawObjs(gy, dispcnt);
    BuildWindows(gy, dispcnt);
    ComposeLine(y, dispcnt, bgOn, bgPrio, gPortFrame, 1);
    /* The presenter also uses this background in non-menu narrow scenes,
       including the blank frame between modes. Never leave last frame's
       palette/fade in the buffer. */
    if (sSceneNarrow || !gPortScreen.wide)
        ComposeLine(y, dispcnt, bgOn, bgPrio, gPortMenuBackground, 0);
    if (sSceneNarrow)
        BuildNarrowSides(gy, dispcnt, bgOn, bgPrio);
    if (sOverlay && gy >= 0 && gy < GBA_SCREEN_H)
        ComposeOverlayLine(gy, dispcnt, bgOn, bgPrio);
}

/* Full-height GBA scenes (menus shown as the GBA picture with side bars):
   what lies beyond the picture's edges, built from the BG layers themselves
   so the bars are the game's own art in its own pixels and palettes. The
   scenery (the lowest enabled BG) continues mirrored, as the hardware's
   horizontal tile flip draws it; a layer above it continues only where it
   reaches the edge as a long horizontal band (a title bar, a banner, a
   panel), and is transparent elsewhere so the scenery shows; the backdrop is
   underneath. The scene's fade applies to the bars too. */
#define NARROW_SIDE_W 96
#define PLTT16_0() (((const uint16_t*)(uintptr_t)GBA_PLTT)[0])
static uint32_t sNarrowSide[2][GBA_SCREEN_H][NARROW_SIDE_W];
/* per row: the colour of the layer in front of the scenery at the picture's
   edge, and whether that row was a band (2), only touched the edge (1) or
   showed the scenery (0) */
static uint32_t sNarrowEdge[2][GBA_SCREEN_H];
static uint8_t sNarrowEdgeKind[2][GBA_SCREEN_H];

/* A box or title is one block of rows touching the edge; its lettering can
   cut some rows short of a band (the Moogle Shop's points box, the title's
   middle rows), but they belong to it, so a block with any band row carries
   every row on, each in its own edge colour. */
/* 2 when the layer in front of the scenery reaches the edge of row y as a
   long band, 1 when it only touches the edge, 0 when the edge shows the
   scenery itself (GBA-size scenes only; -1 otherwise) */
int PortNarrowEdgeKind(int side, int y) {
    if (!sSceneNarrow || y < 0 || y >= GBA_SCREEN_H)
        return -1;
    return sNarrowEdgeKind[side > 0][y];
}

void PortNarrowSidesFinish(void) {
    int side, y;
    for (side = 0; side < 2; side++)
        for (y = 0; y < GBA_SCREEN_H; y++) {
            int a = y, z = y, band = 0, k, d;
            if (!sNarrowEdgeKind[side][y])
                continue;
            while (z + 1 < GBA_SCREEN_H && sNarrowEdgeKind[side][z + 1]) z++;
            for (k = a; k <= z; k++) band |= sNarrowEdgeKind[side][k] == 2;
            if (band)
                for (k = a; k <= z; k++)
                    if (sNarrowEdgeKind[side][k] == 1)
                        for (d = 0; d < NARROW_SIDE_W; d++)
                            sNarrowSide[side][k][d] = sNarrowEdge[side][k];
            y = z;
        }
}

uint32_t PortNarrowSidePixel(int side, int y, int distance) {
    if (y < 0 || y >= GBA_SCREEN_H)
        return 0;
    if (distance >= NARROW_SIDE_W)
        distance = NARROW_SIDE_W - 1 - (distance % NARROW_SIDE_W);
    return sNarrowSide[side > 0][y][distance < 0 ? 0 : distance];
}

static void BuildNarrowSides(int gy, uint16_t dispcnt, const int* bgOn, const int* bgPrio) {
    int side, d, b, scenery = -1, order[4], n = 0, p, flat;
    int x0 = gPortScreen.originX;
    uint16_t bldcnt = IO16(0x50);
    int effect = (bldcnt >> 6) & 3, evy = IO16(0x54) & 31;

    if (gy < 0 || gy >= GBA_SCREEN_H)
        return;
    if (evy > 16)
        evy = 16;
    /* the scenery: the enabled BG drawn last (largest priority, then index) */
    for (b = 0; b < 4; b++)
        if (bgOn[b] && (scenery < 0 || bgPrio[b] > bgPrio[scenery] ||
                        (bgPrio[b] == bgPrio[scenery] && b > scenery)))
            scenery = b;
    for (p = 0; p < 4; p++)
        for (b = 0; b < 4; b++)
            if (bgOn[b] && bgPrio[b] == p)
                order[n++] = b;
    for (side = 0; side < 2; side++) {
        int edge = side ? x0 + GBA_SCREEN_W - 1 : x0, step = side ? -1 : 1;
        uint16_t band[4];
        int bandOk[4];
        for (b = 0; b < 4; b++) {
            int run = 0, k;
            uint16_t c = sBgLine[b][edge];
            bandOk[b] = 0;
            band[b] = c;
            if (!bgOn[b] || b == scenery || c == TRANSPARENT)
                continue;
            for (k = 0; k < 48 && sBgLine[b][edge + k * step] == c; k++)
                run++;
            bandOk[b] = run >= 24;
        }
        /* scenery that is plain next to the edge (two tiles of one colour)
           carries on plain: mirrored, the shapes further in (the Moogle
           Shop's pedestals) would show up again as reflections */
        flat = 0;
        if (scenery >= 0 && sBgLine[scenery][edge] != TRANSPARENT) {
            int k;
            for (k = 0; k < 16 && sBgLine[scenery][edge + k * step] == sBgLine[scenery][edge]; k++) {}
            flat = k == 16;
        }
        sNarrowEdgeKind[side][gy] = 0;
        for (p = 0; p < n && order[p] != scenery; p++) {
            uint16_t c;
            b = order[p];
            if (band[b] == TRANSPARENT)
                continue;
            c = band[b];
            if (effect == 2 && (bldcnt & 0x3F)) c = Brighten(c, evy);
            if (effect == 3 && (bldcnt & 0x3F)) c = Darken(c, evy);
            sNarrowEdge[side][gy] = sColorLut[c & 0x7FFF];
            sNarrowEdgeKind[side][gy] = bandOk[b] ? 2 : 1;
            break;
        }
        for (d = 0; d < NARROW_SIDE_W; d++) {
            uint16_t col = (uint16_t)(PLTT16_0() & 0x7FFF);
            int i, src = flat ? 0 : d < GBA_SCREEN_W ? d : GBA_SCREEN_W - 1;
            for (i = 0; i < n; i++) {
                b = order[i];
                if (b == scenery) {
                    uint16_t c = sBgLine[b][edge + src * step];
                    if (c != TRANSPARENT) { col = c; break; }
                } else if (bandOk[b]) {
                    col = band[b];
                    break;
                }
            }
            if (effect == 2 && (bldcnt & 0x3F)) col = Brighten(col, evy);
            if (effect == 3 && (bldcnt & 0x3F)) col = Darken(col, evy);
            sNarrowSide[side][gy][d] = sColorLut[col & 0x7FFF];
        }
    }
    (void)dispcnt;
}

/* Start of a line: VCOUNT and the V-counter match flag. */
static void LineStart(int line) {
    uint16_t dispstat = IO16(0x04);

    IO16(0x06) = (uint16_t)line;
    IO16(0x04) = (dispstat & ~6) | (((dispstat >> 8) == line) ? 4 : 0);
}

/* End of a line's drawing period. The V-counter interrupt is delivered here
   rather than at the start of the line: handlers typically wait for HBlank
   anyway, and either way their writes take effect from the next line. */
static void HBlank(int line) {
    uint16_t dispstat;

    IO16(0x04) |= 2;
    dispstat = IO16(0x04);
    if ((dispstat & 4) && (dispstat & 0x20))
        PortRaiseIrq(0x0004);
    if (line < GBA_SCREEN_H)
        PortDmaHBlank();
    if (dispstat & 0x10)
        PortRaiseIrq(0x0002);
    IO16(0x04) &= ~2;
}

/* A mode switch asks for its framing before the old picture has gone: the
   change waits for a blank frame of the transition (or half a second), so
   the last frame of the old screen never shows at the new size. */
void PortSceneNarrow(int on) {
    sNarrowWanted = on;
    sNarrowWait = 0;
}

static void UpdateSceneNarrow(uint16_t dispcnt) {
    uint16_t bldcnt = IO16(0x50);
    int blank = (dispcnt & 0x80) || !(dispcnt & 0x1F00)
                || (((bldcnt >> 6) & 3) == 3 && (IO16(0x54) & 31) >= 16 && (bldcnt & 0x1F) == 0x1F);

    if (sSceneNarrow == sNarrowWanted)
        return;
    if (blank || ++sNarrowWait > 30)
        sSceneNarrow = sNarrowWanted;
}

/* The scene is one of the full-screen menus over the field (PortSceneNarrow). */
int PortPpuSceneIsMenu(void) {
    return sSceneNarrow;
}

/* Grow to the active canvas, retaining capacity across menu/world switches.
   Each allocation remains separately aligned. New space is zeroed just as
   the former maximum-sized calloc buffers were; existing pixels survive a
   resize until the next frame renders them. */
void PortCanvasAlloc(void) {
    static size_t capacity;
    size_t n = (size_t)gPortScreen.width * gPortScreen.height;
    uint32_t* frame;
    uint32_t* background;
    uint8_t *bg, *layer, *message;
    uint16_t* obj;
    if (n <= capacity)
        return;
    frame = (uint32_t*)realloc(gPortFrame, n * sizeof(*frame));
    background = (uint32_t*)realloc(gPortMenuBackground, n * sizeof(*background));
    bg = (uint8_t*)realloc(sOccBg, n);
    layer = (uint8_t*)realloc(sOccBgLayer, n);
    message = (uint8_t*)realloc(sMsgMask, n);
    obj = (uint16_t*)realloc(sOccObj, n * sizeof(*obj));
    if (!frame || !background || !bg || !layer || !message || !obj)
        PortFatal("Out of memory for the picture buffers");
    gPortFrame = frame; gPortMenuBackground = background;
    sOccBg = bg; sOccBgLayer = layer; sMsgMask = message; sOccObj = obj;
    memset(frame + capacity, 0, (n - capacity) * sizeof(*frame));
    memset(background + capacity, 0, (n - capacity) * sizeof(*background));
    memset(bg + capacity, 0, n - capacity);
    memset(layer + capacity, 0, n - capacity);
    memset(message + capacity, 0, n - capacity);
    memset(obj + capacity, 0, (n - capacity) * sizeof(*obj));
    capacity = n;
}

void PortPpuBeginFrame(void) {
    uint16_t dispcnt = IO16(0x00);
    int b, any = 0;
#ifdef __ANDROID__
    /* Alpha keeps original pixel text until its portable font backend exists. */
    gPortConfig.hdText = 0;
#endif
    sBgTextCount = 0;

    BuildLut();
    UpdateSceneNarrow(dispcnt);
    for (b = 0; b < 4; b++) {
        sBgLatch[b].valid = ValidateBgLatch(b, dispcnt);
        sBgWorldLatched[b].valid = !sBgLatch[b].valid && ValidateBgWorld(b, dispcnt);
        any |= sBgLatch[b].valid | sBgWorldLatched[b].valid;
    }
    /* Large affine stages (battle arenas) are fully in VRAM and extend as is. */
    for (b = 2; b < 4; b++) {
        int mode = dispcnt & 7;
        if ((dispcnt & (0x100 << b)) && (mode == 2 || (mode == 1 && b == 2)) && (IO16(0x08 + b * 2) >> 14) >= 2)
            any = 1;
    }
    /* the door's spotlight (hitting a door, then room synthesis) is a
       GBA-size scene: shown at the window's height like the other menus,
       never as a small picture at the world's zoom */
    gPortScreen.wide = any && !sSceneNarrow && !(sSpotlight && !(sScreenBgMask & 2u))
                       && (gPortScreen.width > GBA_SCREEN_W || gPortScreen.height > GBA_SCREEN_H)
                       && !(dispcnt & 0x80);
    if (getenv("KHCOM_PPULOG"))
        PortLog("ppu: dispcnt %04x latch %d%d%d%d world %d%d%d%d bgcnt %04x %04x %04x %04x wide %d narrow %d", dispcnt,
                sBgLatch[0].valid, sBgLatch[1].valid, sBgLatch[2].valid, sBgLatch[3].valid, sBgWorldLatched[0].valid,
                sBgWorldLatched[1].valid, sBgWorldLatched[2].valid, sBgWorldLatched[3].valid, IO16(0x08), IO16(0x0A),
                IO16(0x0C), IO16(0x0E), gPortScreen.wide, sSceneNarrow);
    sHudLayer = gPortScreen.wide && gPortHudScale > 0 && gPortHudW >= GBA_SCREEN_W;
    sHdText = gPortConfig.hdText;
    if (sHudLayer || sHdText) {
        memset(sOccBg, 4, (size_t)gPortScreen.width * gPortScreen.height);
        memset(sOccBgLayer, 4, (size_t)gPortScreen.width * gPortScreen.height);
        memset(sOccObj, 0xFF, (size_t)gPortScreen.width * gPortScreen.height * 2);
    }
    sOverlay = gPortScreenLayer;
    for (b = 0; b < 4; b++) {
        int m = dispcnt & 7;
        int arena = (m == 2 || (m == 1 && b == 2)) && b >= 2 && (IO16(0x08 + b * 2) >> 14) >= 2;
        /* Split menus may use the engine's map-block API too; those blocks
           describe UI pages, not a world that should remain under the overlay. */
        sScreenBg[b] = sOverlay && !(sSpotlight && b == 0) &&
            ((sScreenBgMask & (1u << b)) || sBgSplit[b] ||
             (!sBgLatch[b].valid && !sBgWorldLatched[b].valid && !arena));
    }
    if (sOverlay)
        memset(gPortOverlay, 0, (size_t)gPortOverlayW * GBA_SCREEN_H * 4);
    for (b = 0; b < 4; b++) sWorldPadding[b] = WorldPadding(b, &sBgLatch[b]);
    if (gPortScreen.wide) {
        sLeft = -gPortScreen.originX;
        sRight = gPortScreen.width - gPortScreen.originX;
        sTop = -gPortScreen.originY;
        sBottom = gPortScreen.height - gPortScreen.originY;
    } else {
        sLeft = 0;
        sRight = GBA_SCREEN_W;
        sTop = 0;
        sBottom = GBA_SCREEN_H;
    }
}

/* Draw the visible lines, running the per-line hardware events in between. */
void PortPpuRenderFrame(void) {
    int y, gy;
    int w = gPortScreen.width;

    PortPpuBeginFrame();
    LatchAffine(1);

    /* Lines above the original picture: state of line 0. */
    for (y = 0; y < gPortScreen.originY; y++) {
        gy = y - gPortScreen.originY;
        if (gy < sTop) {
            memset(gPortFrame + y * w, 0, w * 4);
            continue;
        }
        {
            int32_t sx[2] = { sAffX[0], sAffX[1] }, sy[2] = { sAffY[0], sAffY[1] };
            int a;
            for (a = 0; a < 2; a++) {
                sAffX[a] += (int16_t)IO16(0x22 + a * 0x10) * gy;
                sAffY[a] += (int16_t)IO16(0x26 + a * 0x10) * gy;
            }
            RenderLine(y, gy);
            for (a = 0; a < 2; a++) {
                sAffX[a] = sx[a];
                sAffY[a] = sy[a];
            }
        }
    }

    for (gy = 0; gy < GBA_SCREEN_H; gy++) {
        LineStart(gy);
        LatchAffine(0);
        RenderLine(gy + gPortScreen.originY, gy);
        StepAffine(1);
        HBlank(gy);
    }

    /* Lines below the original picture: state after line 159. */
    for (y = gPortScreen.originY + GBA_SCREEN_H; y < gPortScreen.height; y++) {
        gy = y - gPortScreen.originY;
        if (gy >= sBottom) {
            memset(gPortFrame + y * w, 0, w * 4);
            memset(gPortMenuBackground + y * w, 0, w * 4);
            continue;
        }
        RenderLine(y, gy);
        StepAffine(1);
    }
}

/* Remaining lines of the frame (VBlank period) after the VBlank interrupt. */
void PortPpuVBlankLines(void) {
    int line;

    for (line = GBA_SCREEN_H + 1; line < 228; line++) {
        LineStart(line);
        HBlank(line);
    }
    IO16(0x06) = 0;
}

/* ---- HUD layer ----------------------------------------------------------------
 * HUD sprites (drawn between PortHudBegin/End) are rendered into their own
 * ARGB buffer, gPortHudW x gPortHudH, which the presenter scales by
 * gPortHudScale: larger than the world while staying pixel-exact. Each
 * sprite keeps its distance to the screen edge it is anchored to.
 */
void PortMenuTabBg(int side, int bg, int x, int y) {
    int i = side > 0;
    sMenuPend.tabBg[i] = bg; sMenuPend.tabX[i] = x; sMenuPend.tabY[i] = y;
    sMenuPend.tabFrame = NULL;
}
void PortMenuTabSprite(void* frame, void* tiles, void* palette) {
    sMenuPend.tabFrame = frame; sMenuPend.tabTiles = tiles; sMenuPend.tabPalette = palette;
}

void PortMenuHeaderSource(void* frame, void* tiles, void* palette) {
    sMenuPend.headerFrame = frame;
    sMenuPend.headerTiles = tiles;
    sMenuPend.headerPalette = palette;
    if (!frame) {
        memset(sMenuPend.bands, 0, sizeof(sMenuPend.bands));
        sMenuPend.tabFrame = NULL;
        sMenuPend.tabBg[0] = sMenuPend.tabBg[1] = -1;
        sMenuShown = sMenuPend; /* a new mode: nothing of the old one stays */
        sMenuModeStart = PortFrameCount();
    }
}

static int ObjColor(uint16_t a0, uint16_t a2, int tx, int ty, int ow, int mapping1d) {
    int bpp8 = (a0 >> 13) & 1;
    int tileBase = a2 & 0x3FF;
    int tile, ci;
    uint32_t off;

    if (bpp8) {
        tile = mapping1d ? tileBase + ((ty >> 3) * (ow >> 3) + (tx >> 3)) * 2 : tileBase + (ty >> 3) * 32 + (tx >> 3) * 2;
        off = 0x10000 + (tile & 0x3FF) * 32 + (ty & 7) * 8 + (tx & 7);
        ci = VRAM8[off];
        return ci ? (PLTT16[256 + ci] & 0x7FFF) : -1;
    }
    tile = mapping1d ? tileBase + (ty >> 3) * (ow >> 3) + (tx >> 3) : tileBase + (ty >> 3) * 32 + (tx >> 3);
    off = 0x10000 + (tile & 0x3FF) * 32 + (ty & 7) * 4 + ((tx & 7) >> 1);
    ci = (tx & 1) ? (VRAM8[off] >> 4) : (VRAM8[off] & 15);
    return ci ? (PLTT16[256 + (a2 >> 12) * 16 + ci] & 0x7FFF) : -1;
}

/* Colour of the header asset at (tx, y), tx counted from its left edge; -1
   when transparent or not drawable. Neither cursor OAM nor the finished
   framebuffer enters it. */
static int MenuSpriteColor(const uint16_t* frame, const ObjTiles* tiles,
                           const ObjPalette* palette, int y, int col0, int* top, int* bottom) {
    const uint16_t* p = frame;
    int n, i, left = 32767, offset = 0, col = -1;
    if (!p || !tiles || !palette ||
        tiles->self != tiles || palette->self != palette ||
        (IO16(0) & 0x80) || !(IO16(0) & 0x1000))
        return -2;
    n = *p++;
    if (n > 128) return -2;
    for (i = 0; i < n; i++) {
        int x = p[i * 3 + 1] & 511, oy = p[i * 3] & 255, shape = p[i * 3] >> 14;
        if (x >= 256) x -= 512;
        if (x < left) left = x;
        if (oy >= 128) oy -= 256;
        if (top && shape < 3) {
            int oh = sObjSize[shape][p[i * 3 + 1] >> 14][1];
            if (oy < *top) *top = oy;
            if (oy + oh > *bottom) *bottom = oy + oh;
        }
    }
    for (i = 0; i < n; i++) {
        uint16_t a0 = p[i * 3], a1 = p[i * 3 + 1], a2 = p[i * 3 + 2];
        int shape = a0 >> 14, size = a1 >> 14, x = a1 & 511, oy = a0 & 255;
        int ow, oh, tx, ty, tile;
        if (shape >= 3) continue;
        ow = sObjSize[shape][size][0]; oh = sObjSize[shape][size][1];
        if (x >= 256) x -= 512;
        if (oy >= 128) oy -= 256;
        tx = left + col0 - x; ty = y - oy;
        tile = tiles->allocated ? offset : (a2 & 1023);
        offset += (ow * oh / 64) * ((a0 & 0x2000) ? 2 : 1);
        if (tx < 0 || tx >= ow || ty < 0 || ty >= oh) continue;
        if (a1 & 0x1000) tx = ow - 1 - tx;
        if (a1 & 0x2000) ty = oh - 1 - ty;
        a2 = ((tile + tiles->index) & 1023) |
             (((a2 >> 12) + palette->index) << 12);
        col = ObjColor(a0, a2, tx, ty, ow, (IO16(0) & 0x40) != 0);
        if (col >= 0) break;
    }
    return col;
}

/* A repeatable piece of an asset, independent of its animated screen
   position: columns col0 and col0 + 1 from its left end. */
static uint32_t MenuSpritePixel(const uint16_t* frame, const ObjTiles* tiles,
                                const ObjPalette* palette, int y, int phase, int col0) {
    int col = MenuSpriteColor(frame, tiles, palette, y, col0 + (phase & 1), NULL, NULL);
    if (col < 0) return 0;
    if (IO16(0x50) & 0x10) {
        int effect = (IO16(0x50) >> 6) & 3, evy = IO16(0x54) & 31;
        if (evy > 16) evy = 16;
        if (effect == 2) col = Brighten(col, evy);
        if (effect == 3) col = Darken(col, evy);
    }
    return sColorLut[col];
}

/* The header's band: the pair of columns near its left end with the fewest
   colour changes top to bottom, so a title that starts at the very edge
   (US "WORLD CARDS") does not lend a letter stroke to the band. Its colours
   are kept: outside Europe the title is redrawn on a BG once it has slid in
   and its sprite palette is released, while the band must stay. */
static int sHeaderBand[2][32];

static int HeaderPick(void) {
    static const void* key[3];
    static int pick, valid;
    static uint32_t stamp;

    /* once a frame: the asset's tiles and palette arrive after it is first drawn */
    if (stamp != PortFrameCount() || key[0] != sMenuHeaderFrame || key[1] != sMenuHeaderTiles ||
        key[2] != sMenuHeaderPalette) {
        int top = 32767, bottom = -32767, best = 1 << 30, k, j, yy;
        stamp = PortFrameCount();
        if (MenuSpriteColor(sMenuHeaderFrame, sMenuHeaderTiles, sMenuHeaderPalette, 0, 0, &top, &bottom) == -2)
            return sMenuHeaderFrame && key[0] == sMenuHeaderFrame && valid ? pick : -1;
        valid = 0;
        pick = 0;
        /* most opaque first (the band, not its transparent ends or the
           arrow), then fewest changes (no lettering) */
        for (k = 0; k < 96; k += 2) {
            int changes = 0, opaque = 0, score;
            for (j = 0; j < 2; j++) {
                int prev = -3;
                for (yy = top; yy < bottom && yy < 32; yy++) {
                    int c = MenuSpriteColor(sMenuHeaderFrame, sMenuHeaderTiles, sMenuHeaderPalette, yy, k + j, NULL, NULL);
                    if (c >= 0) opaque++;
                    if (yy > top && c != prev) changes++;
                    prev = c;
                }
            }
            score = changes - opaque * 64;
            if (opaque > 0 && score < best) {
                best = score;
                pick = k;
            }
        }
        for (j = 0; j < 2; j++)
            for (yy = 0; yy < 32; yy++)
                sHeaderBand[j][yy] = MenuSpriteColor(sMenuHeaderFrame, sMenuHeaderTiles, sMenuHeaderPalette, yy, pick + j, NULL, NULL);
        key[0] = sMenuHeaderFrame; key[1] = sMenuHeaderTiles; key[2] = sMenuHeaderPalette;
        valid = 1;
    }
    return valid || key[0] == sMenuHeaderFrame ? pick : -1;
}

static int HeaderBandColor(int y, int phase) {
    if (HeaderPick() < 0 || y < 0 || y >= 32)
        return -1;
    return sHeaderBand[phase & 1][y];
}

static uint32_t HeaderPixelRaw(int y, int phase);

/* Is the header on the picture now? Its band must be in the picture's left
   column: while a menu is still coming in (before its title has appeared)
   the margin must not show the band. Checked once a frame, on GBA-size
   pictures only. */
static int HeaderOnScreen(void) {
    static uint32_t checked = ~0u;
    static int shown;
    int yy, opaque = 0, match = 0;
    if (gPortScreen.wide)
        return 1;
    if (checked == PortFrameCount())
        return shown;
    checked = PortFrameCount();
    for (yy = 0; yy < 16 && gPortScreen.originY + yy < gPortScreen.height; yy++) {
        uint32_t a = HeaderPixelRaw(yy, 0) & 0xFFFFFF, b = HeaderPixelRaw(yy, 1) & 0xFFFFFF;
        uint32_t px = gPortFrame[(gPortScreen.originY + yy) * gPortScreen.width + gPortScreen.originX] & 0xFFFFFF;
        if (!a && !b)
            continue;
        opaque++;
        match += px == a || px == b;
    }
    shown = opaque > 0 && match * 2 >= opaque;
    return shown;
}

/* Where the header sprite was drawn (DrawMenuHeader), so its extension in
   the margin travels with it: the margin shows the sprite's own pixels
   where it reaches past the picture's edge, and the band only to its left,
   as if the screen had always been that wide. */
void PortMenuHeaderAt(int x) {
    sMenuPend.headerX = x;
    sMenuPend.headerDrawn = 1;
}

static int HeaderLeft(void) {
    const uint16_t* p = sMenuHeaderFrame;
    int n, i, left = 32767;
    if (!p) return 0;
    n = *p++;
    if (n <= 0 || n > 128) return 0;
    for (i = 0; i < n; i++) {
        int x = p[i * 3 + 1] & 511;
        if (x >= 256) x -= 512;
        if (x < left) left = x;
    }
    return left;
}

uint32_t PortMenuHeaderPixelAt(int y, int d) {
    int c = -1 - d, s;
    if (!sMenuHeaderFrame || !sMenuShown.headerDrawn)
        return PortMenuHeaderPixel(y, d);
    s = c - sMenuShown.headerX - HeaderLeft();
    if (s >= 0)
        return MenuSpritePixel(sMenuHeaderFrame, sMenuHeaderTiles, sMenuHeaderPalette, y, 0, s);
    return HeaderPixelRaw(y, d);
}

uint32_t PortMenuHeaderPixel(int y, int phase) {
    if (!sMenuHeaderFrame || !HeaderOnScreen())
        return 0;
    return HeaderPixelRaw(y, phase);
}

static uint32_t HeaderPixelRaw(int y, int phase) {
    int col;
    if (!sMenuHeaderFrame)
        return 0;
    col = HeaderBandColor(y, phase);
    if (col < 0) return 0;
    if (IO16(0x50) & 0x10) {
        int effect = (IO16(0x50) >> 6) & 3, evy = IO16(0x54) & 31;
        if (evy > 16) evy = 16;
        if (effect == 2) col = Brighten(col, evy);
        if (effect == 3) col = Darken(col, evy);
    }
    return sColorLut[col];
}

void PortMenuBandSource(int band, int y, void* frame, void* tiles, void* palette) {
    if ((unsigned)band >= 2) return;
    sMenuPend.bands[band].frame = frame;
    sMenuPend.bands[band].tiles = tiles;
    sMenuPend.bands[band].palette = palette;
    sMenuPend.bands[band].y = y;
}

uint32_t PortMenuBandPixel(int y, int phase) {
    int i;
    for (i = 0; i < 2; i++) {
        const MenuBandSource* band = &sMenuBands[i];
        uint32_t color = MenuSpritePixel(band->frame, band->tiles, band->palette, y - band->y, phase, 0);
        if (color) return color;
    }
    return 0;
}

uint32_t PortMenuTabPixel(int y, int phase, int side) {
    int i = side > 0, bg = sMenuTabBg[i], x, yy, ci, col;
    uint16_t cnt, entry;
    uint32_t map, chr, address;
    if (sMenuTabFrame && side < 0)
        return MenuSpritePixel(sMenuTabFrame, sMenuTabTiles, sMenuTabPalette, y - 16, 0, 0);
    if (bg < 0 || y < 16 || y >= 32 || (IO16(0) & 0x80)) return 0;
    cnt = IO16(8 + bg * 2);
    map = ((cnt >> 8) & 31) * 2048; chr = ((cnt >> 2) & 3) * 16384;
    /* Read the clean end of the authored tab tile, ignoring animated scroll
       and all foreground OAM. It remains the same piece when the hand moves. */
    x = sMenuTabX[i]; yy = sMenuTabY[i] + y - 16;
    entry = ((const uint16_t*)VRAM8)[(map + ((yy >> 3) * 32 + (x >> 3)) * 2) / 2];
    x &= 7; yy &= 7;
    if (entry & 0x400) x = 7 - x;
    if (entry & 0x800) yy = 7 - yy;
    address = chr + (entry & 1023) * ((cnt & 0x80) ? 64 : 32);
    if (cnt & 0x80) {
        ci = VRAM8[address + yy * 8 + x];
        col = ci;
    } else {
        int packed = VRAM8[address + yy * 4 + x / 2];
        ci = (x & 1) ? packed >> 4 : packed & 15;
        col = (entry >> 12) * 16 + ci;
    }
    if (!ci) return 0;
    col = PLTT16[col] & 0x7FFF;
    if (IO16(0x50) & (1 << bg)) {
        int effect = (IO16(0x50) >> 6) & 3, evy = IO16(0x54) & 31;
        if (evy > 16) evy = 16;
        if (effect == 2) col = Brighten(col, evy);
        if (effect == 3) col = Darken(col, evy);
    }
    return sColorLut[col];
}

/* The backdrop colour (palette 0), as displayed. */
uint32_t PortPpuBackdrop(void) {
    return sColorLut[PLTT16[0] & 0x7FFF];
}

void PortPpuRenderHud(uint32_t* buf) {
    uint16_t dispcnt = IO16(0x00);
    uint16_t bldcnt = IO16(0x50);
    int effect = (bldcnt >> 6) & 3, evy = IO16(0x54) & 31;
    int mapping1d = (dispcnt >> 6) & 1;
    int w = gPortHudW, h = gPortHudH;
    int i;

    sEnemyHudRect[0] = w; sEnemyHudRect[1] = h;
    PortHdHudSpriteBegin();
    sEnemyHudRect[2] = sEnemyHudRect[3] = -1;
    sEnemyLabelRect[0] = w; sEnemyLabelRect[1] = h;
    sEnemyLabelRect[2] = sEnemyLabelRect[3] = -1;
    sEnemyLabelColor = 0;
    sEnemyBarRect[0] = w; sEnemyBarRect[1] = h;
    sPlayerBarRect[0] = w; sPlayerBarRect[1] = h;
    sPlayerFullHp = 0;
    sPlayerFrameRect[0] = w; sPlayerFrameRect[1] = h;
    sPlayerFrameRect[2] = sPlayerFrameRect[3] = -1;
    sPlayerBarRect[2] = sPlayerBarRect[3] = -1;
    memset(sPlayerBarRows, 0, sizeof(sPlayerBarRows));
    if (gPortConfig.hdHud && (size_t)w * 32 > sPlayerBarMaskSize) {
        uint8_t* mask = realloc(sPlayerBarMask, (size_t)w * 32);
        if (mask) { sPlayerBarMask = mask; sPlayerBarMaskSize = (size_t)w * 32; }
    }
    if (sPlayerBarMask && (size_t)w * 32 <= sPlayerBarMaskSize)
        memset(sPlayerBarMask, 0, (size_t)w * 32);
    sEnemyBarRect[2] = sEnemyBarRect[3] = -1;
    memset(sEnemyBarRows, 0, sizeof(sEnemyBarRows));
    sHudDigitCount = 0;
    if (gPortConfig.hdHud && (size_t)w * h > sHudDigitOwnerSize) {
        uint8_t* owners = realloc(sHudDigitOwners, (size_t)w * h);
        if (owners) { sHudDigitOwners = owners; sHudDigitOwnerSize = (size_t)w * h; }
    }
    if (sHudDigitOwners && (size_t)w * h <= sHudDigitOwnerSize)
        memset(sHudDigitOwners, 0, (size_t)w * h);
    if (gPortConfig.hdHud && (size_t)w * h > sEnemyBarMaskSize) {
        uint8_t* mask = realloc(sEnemyBarMask, (size_t)w * h);
        if (mask) { sEnemyBarMask = mask; sEnemyBarMaskSize = (size_t)w * h; }
    }
    if (sEnemyBarMask && (size_t)w * h <= sEnemyBarMaskSize)
        memset(sEnemyBarMask, 0, (size_t)w * h);
    memset(buf, 0, (size_t)w * h * 4);
    if (!sHudLayer || (dispcnt & 0x80) || !(dispcnt & 0x1000))
        return;
    if (evy > 16)
        evy = 16;

    for (i = 127; i >= 0; i--) {
        uint16_t a0 = OAM16[i * 4 + 0], a1 = OAM16[i * 4 + 1], a2 = OAM16[i * 4 + 2];
        int affine = (a0 >> 8) & 1, dbl = (a0 >> 9) & 1, mode = (a0 >> 10) & 3;
        int shape = (a0 >> 14) & 3, size = (a1 >> 14) & 3;
        int ow, oh, bw, bh, ox, oy, xg, yg, hx, hy, sx, sy;
        int16_t pa = 0x100, pb = 0, pc = 0, pd = 0x100;
        const SpriteTag* tag = &sOamTag[i];
        PortHudDigit* digit = NULL;
        uint32_t* rawHud = NULL;
        int hdSprite = 0;

        if (!tag->hud || (!affine && dbl) || shape == 3 || mode >= 2 ||
            (HdTextGlyph(i) && tag->style != 2))
            continue;
        ow = sObjSize[shape][size][0];
        oh = sObjSize[shape][size][1];
        if (gPortConfig.hdHud && sHudDigitOwners && (size_t)w * h <= sHudDigitOwnerSize &&
            tag->digit && tag->digit <= 10 && sHudDigitCount < 128) {
            if (!sHudDigits) sHudDigits = calloc(128, sizeof(*sHudDigits));
            if (sHudDigits) {
                digit = &sHudDigits[sHudDigitCount];
                digit->x = w; digit->y = h; digit->w = digit->h = -1;
                digit->code = '0' + tag->digit - 1;
                digit->slot = i;
                digit->color = 0;
            }
        }
        {
            uint32_t* reference = PortHdHudExportBuffer();
            rawHud = reference;
            if (reference) {
                int xx, yy;
                for (yy = 0; yy < oh; yy++) for (xx = 0; xx < ow; xx++) {
                    int c = ObjColor(a0, a2, xx, yy, ow, mapping1d);
                    reference[yy * ow + xx] = c < 0 ? 0 : sColorLut[c];
                }
                PortHdHudExportSprite(ow, oh, tag->hdHudPart, tag->ax, tag->ay);
            }
        }
        bw = ow << (affine && dbl);
        bh = oh << (affine && dbl);
        oy = a0 & 0xFF;
        ox = a1 & 0x1FF;
        if ((sOamExt[i].x & 0x1FF) == ox && (sOamExt[i].y & 0xFF) == oy) {
            ox = sOamExt[i].x;
            oy = sOamExt[i].y;
        }
        /* back to GBA-screen coordinates, then onto the HUD canvas */
        xg = ox - (tag->ax == 2 ? 0 : tag->ax) * gPortScreen.originX;
        yg = oy - tag->ay * gPortScreen.originY;
        hx = tag->ax == 2 ? HudWorldX(xg, bw, w)
             : tag->ax < 0 ? xg : (tag->ax > 0 ? w - (GBA_SCREEN_W - xg) : xg + (w - GBA_SCREEN_W) / 2);
        hy = tag->ay < 0 ? yg : (tag->ay > 0 ? h - (GBA_SCREEN_H - yg) : yg + (h - GBA_SCREEN_H) / 2);
        if (tag->ay > 0)
            hy -= HudRaise();
        if (!affine && !tag->hdHudPart && !tag->digit && sHudDigitOwners &&
            (size_t)w*h <= sHudDigitOwnerSize)
            hdSprite = PortHdHudSpriteRegister(rawHud, ow, oh, i, hx, hy,
                ((a1 & 0x1000) ? 1 : 0) | ((a1 & 0x2000) ? 2 : 0), mode == 1 ? 0xA0 : 255);
        {
            const char* frame = getenv("KHCOM_HUD_LAYOUT");
            if (frame && (uint32_t)atoi(frame) == PortFrameCount())
                PortLog("hud-layout: frame=%u slot=%d x=%d y=%d w=%d h=%d tile=%d palette=%d part=%d affine=%d",
                    PortFrameCount(), i, hx, hy, bw, bh, a2 & 1023, a2 >> 12, tag->hdHudPart, affine);
        }
        if (affine) {
            const uint16_t* p = OAM16 + ((a1 >> 9) & 31) * 16;
            pa = (int16_t)p[3];
            pb = (int16_t)p[7];
            pc = (int16_t)p[11];
            pd = (int16_t)p[15];
        }
        for (sy = 0; sy < bh; sy++) {
            int py = hy + sy;
            if (py < 0 || py >= h)
                continue;
            for (sx = 0; sx < bw; sx++) {
                int px = hx + sx, tx, ty, col, digitInk = 0, barInk = 0;
                uint32_t argb;
                if (px < 0 || px >= w)
                    continue;
                if (affine) {
                    int cx = sx - bw / 2, cy = sy - bh / 2;
                    tx = ((pa * cx + pb * cy) >> 8) + ow / 2;
                    ty = ((pc * cx + pd * cy) >> 8) + oh / 2;
                    if (tx < 0 || ty < 0 || tx >= ow || ty >= oh)
                        continue;
                } else {
                    tx = (a1 & 0x1000) ? ow - 1 - sx : sx;
                    ty = (a1 & 0x2000) ? oh - 1 - sy : sy;
                }
                col = ObjColor(a0, a2, tx, ty, ow, mapping1d);
                if (col < 0)
                    continue;
                digitInk = digit && ((col & 31) >= 22 || ((col >> 5) & 31) >= 22 || ((col >> 10) & 31) >= 22);
                if (gPortConfig.hdHud && (tag->hdHudPart == 4 || tag->hdHudPart == 6) && py < 32 && sPlayerBarMask &&
                    (size_t)w * 32 <= sPlayerBarMaskSize && sHudDigitOwners && (size_t)w * h <= sHudDigitOwnerSize) {
                    int r = col & 31, g = (col >> 5) & 31, b = (col >> 10) & 31;
                    int high = r > g ? r : g, low = r < g ? r : g;
                    if (b > high) high = b;
                    if (b < low) low = b;
                    barInk = high - low > 3;
                }
                if (gPortConfig.hdHud && tag->hdHudPart == 3 && sEnemyBarMask && sHudDigitOwners && py < 32 &&
                    (size_t)w * h <= sEnemyBarMaskSize && (size_t)w * h <= sHudDigitOwnerSize) {
                    int r = col & 31, g = (col >> 5) & 31, b = (col >> 10) & 31;
                    int high = r > g ? r : g, low = r < g ? r : g;
                    if (b > high) high = b;
                    if (b < low) low = b;
                    barInk = high - low > 3;
                }
                if (HdTextGlyph(i) && tag->style == 2 &&
                    (col == (PLTT16[256 + (a2 >> 12) * 16 + 14] & 0x7FFF) ||
                     col == (PLTT16[256 + (a2 >> 12) * 16 + 15] & 0x7FFF)))
                    col = PLTT16[256 + (a2 >> 12) * 16 + 13] & 0x7FFF;
                {
                    /* hidden where the cartridge draws something in front */
                    int cx = ox + sx + gPortScreen.originX, cy = oy + sy + gPortScreen.originY;
                    int prio = (a2 >> 10) & 3;
                    if (cx >= 0 && cy >= 0 && cx < gPortScreen.width && cy < gPortScreen.height) {
                        int k = cy * gPortScreen.width + cx;
                        if (sOccBg[k] < prio || sOccObj[k] < prio * 128 + i)
                            continue;
                    }
                }
                if (gPortConfig.hdHud && sHudDigitOwners && (size_t)w * h <= sHudDigitOwnerSize)
                    sHudDigitOwners[py * w + px] = i + 1;
                if (hdSprite) continue;
                if (tag->hdHudPart == 5 && px >= 31 && PortHdHudPlayerFrameReady()) {
                    int r = col & 31, g = (col >> 5) & 31, b = (col >> 10) & 31;
                    int high = r > g ? r : g, low = r < g ? r : g;
                    if (b > high) high = b;
                    if (b < low) low = b;
                    if (high - low <= 3 && high > 0) {
                        if (px < sPlayerFrameRect[0]) sPlayerFrameRect[0] = px;
                        if (py < sPlayerFrameRect[1]) sPlayerFrameRect[1] = py;
                        if (px > sPlayerFrameRect[2]) sPlayerFrameRect[2] = px;
                        if (py > sPlayerFrameRect[3]) sPlayerFrameRect[3] = py;
                        continue;
                    }
                }
                if (gPortConfig.hdHud && (tag->hdHudPart == 1 || tag->hdHudPart == 2)) {
                    int r = col & 31, g = (col >> 5) & 31, b = (col >> 10) & 31;
                    int high = r > g ? r : g, low = r < g ? r : g;
                    if (b > high) high = b;
                    if (b < low) low = b;
                    if (px < sEnemyHudRect[0]) sEnemyHudRect[0] = px;
                    if (py < sEnemyHudRect[1]) sEnemyHudRect[1] = py;
                    if (px > sEnemyHudRect[2]) sEnemyHudRect[2] = px;
                    if (py > sEnemyHudRect[3]) sEnemyHudRect[3] = py;
                    if (tag->hdHudPart == 1 && px >= w - 20 && high - low > 3 && PortHdHudLettersReady()) {
                        uint32_t face = sColorLut[col];
                        if (px < sEnemyLabelRect[0]) sEnemyLabelRect[0] = px;
                        if (py < sEnemyLabelRect[1]) sEnemyLabelRect[1] = py;
                        if (px > sEnemyLabelRect[2]) sEnemyLabelRect[2] = px;
                        if (py > sEnemyLabelRect[3]) sEnemyLabelRect[3] = py;
                        if ((face & 0xFFFFFF) > (sEnemyLabelColor & 0xFFFFFF)) sEnemyLabelColor = face;
                        continue;
                    }
                    /* Replace only the neutral frame. Coloured lettering and
                       lower HP layers retain the cartridge's exact pixels. */
                    /* Native black pixels also clip the live bar beneath
                       the lettering; keep that occlusion exactly intact. */
                    if (high - low <= 3 && high != 0)
                        continue;
                }
                if (bldcnt & 0x10) {
                    if (effect == 2)
                        col = Brighten((uint16_t)col, evy);
                    else if (effect == 3)
                        col = Darken((uint16_t)col, evy);
                }
                argb = sColorLut[col];
                if (barInk) {
                    if (tag->hdHudPart == 4 || tag->hdHudPart == 6) {
                        sPlayerFullHp = tag->hdHudPart == 6;
                        sPlayerBarMask[py * w + px] = 1;
                        sPlayerBarSlot = i;
                        if (px < sPlayerBarRect[0]) sPlayerBarRect[0] = px;
                        if (py < sPlayerBarRect[1]) sPlayerBarRect[1] = py;
                        if (px > sPlayerBarRect[2]) sPlayerBarRect[2] = px;
                        if (py > sPlayerBarRect[3]) sPlayerBarRect[3] = py;
                        sPlayerBarRows[py] = argb;
                        continue;
                    }
                    sEnemyBarMask[py * w + px] = 1;
                    sEnemyBarSlot = i;
                    if (px < sEnemyBarRect[0]) sEnemyBarRect[0] = px;
                    if (py < sEnemyBarRect[1]) sEnemyBarRect[1] = py;
                    if (px > sEnemyBarRect[2]) sEnemyBarRect[2] = px;
                    if (py > sEnemyBarRect[3]) sEnemyBarRect[3] = py;
                    sEnemyBarRows[py] = argb;
                    continue;
                }
                if (gPortConfig.hdHud && sHudDigitOwners && (size_t)w * h <= sHudDigitOwnerSize)
                    sHudDigitOwners[py * w + px] = i + 1;
                if (digitInk) {
                    if (px < digit->x) digit->x = px;
                    if (py < digit->y) digit->y = py;
                    if (px > digit->w) digit->w = px;
                    if (py > digit->h) digit->h = py;
                    if ((argb & 0xFFFFFF) > (digit->color & 0xFFFFFF)) digit->color = argb;
                    continue;
                }
                if (mode == 1)
                    argb = (argb & 0x00FFFFFFu) | 0xA0000000u;
                buf[py * w + px] = argb;
            }
        }
        if (digit && digit->w >= digit->x) {
            digit->w -= digit->x - 1; digit->h -= digit->y - 1;
            sHudDigitCount++;
        }
    }
}

/* HD text glyphs of one layer (0 world canvas, 1 HUD canvas, 2 screen layer), front last. */
int PortPpuTextGlyphs(PortTextGlyph* out, int max, int hud) {
    uint16_t dispcnt = IO16(0x00);
    uint16_t bldcnt = IO16(0x50);
    int effect = (bldcnt >> 6) & 3, evy = IO16(0x54) & 31;
    int n = 0, i;

    if (!sHdText || (dispcnt & 0x80))
        return 0;
    if (evy > 16)
        evy = 16;
    /* BG numbers enter before OBJ text, in the same back-to-front order as
       their authored backgrounds. Their panel pixels still obey windows. */
    {
        int priority, bg, j;
        for (priority = 3; priority >= 0; priority--) for (bg = 3; bg >= 0; bg--)
            for (j = 0; j < sBgTextCount && n < max; j++) {
                const BgTextGlyph* source = &sBgTextGlyphs[j];
                const PortTextGlyph* glyph = &source->glyph;
                int layer = source->screen ? 2 : 0;
                int width = source->screen ? gPortOverlayW : gPortScreen.width;
                int height = source->screen ? GBA_SCREEN_H : gPortScreen.height;
                int px = glyph->x + 4, py = glyph->y + 4, at;
                const uint8_t* occBg = source->screen ? sScreenOccBg : sOccBg;
                const uint8_t* occLayer = source->screen ? sScreenOccBgLayer : sOccBgLayer;
                const uint16_t* occObj = source->screen ? sScreenOccObj : sOccObj;
                uint16_t face, shadow;
                if (source->priority != priority || source->bg != bg || layer != hud ||
                    px < 0 || px >= width || py < 0 || py >= height) continue;
                at = py * width + px;
                if ((occBg[at] == 0 && occObj[at] == 0) || occBg[at] < priority ||
                    (occBg[at] == priority && occLayer[at] < bg) ||
                    occObj[at] < (priority + 1) * 128) continue; /* OBJ wins ties with BG. */
                out[n] = *glyph;
                /* a window over part of the cell (a menu opened beside the
                   number): only the columns left uncovered are drawn */
                {
                    int c0 = 4, c1 = 4, row = py * width;
                    #define BG_TEXT_SHOWN(cx) (glyph->x + (cx) >= 0 && glyph->x + (cx) < width &&                         !((occBg[row + glyph->x + (cx)] == 0 && occObj[row + glyph->x + (cx)] == 0) ||                           occBg[row + glyph->x + (cx)] < priority ||                           (occBg[row + glyph->x + (cx)] == priority && occLayer[row + glyph->x + (cx)] < bg) ||                           occObj[row + glyph->x + (cx)] < (priority + 1) * 128))
                    while (c0 > 0 && BG_TEXT_SHOWN(c0 - 1)) c0--;
                    while (c1 < 8 && BG_TEXT_SHOWN(c1)) c1++;
                    #undef BG_TEXT_SHOWN
                    out[n].clip0 = (uint8_t)c0;
                    out[n].clip1 = (uint8_t)(c0 == 0 && c1 == 8 ? 0 : c1);
                }
                face = (uint16_t)glyph->face; shadow = (uint16_t)glyph->shadow;
                if (bldcnt & (1 << bg)) {
                    if (effect == 2) { face = Brighten(face, evy); shadow = Brighten(shadow, evy); }
                    if (effect == 3) { face = Darken(face, evy); shadow = Darken(shadow, evy); }
                }
                out[n].face = sColorLut[face]; out[n].shadow = sColorLut[shadow];
                n++;
            }
    }
    for (i = 127; i >= 0 && n < max && (dispcnt & 0x1000); i--) {
        uint16_t a0 = OAM16[i * 4 + 0], a1 = OAM16[i * 4 + 1], a2 = OAM16[i * 4 + 2];
        const SpriteTag* tag = &sOamTag[i];
        int onHud = sHudLayer && tag->hud;
        int onScreen = sOverlay && tag->screen;
        int layer = onScreen ? 2 : onHud;
        int ox, oy, bank, k;
        uint16_t col[2];

        if (!HdTextGlyph(i) || layer != hud || (a0 & 0x300) == 0x200 || ((a0 >> 10) & 3) >= 2)
            continue;
        oy = a0 & 0xFF;
        ox = a1 & 0x1FF;
        if ((sOamExt[i].x & 0x1FF) == ox && (sOamExt[i].y & 0xFF) == oy) {
            ox = sOamExt[i].x;
            oy = sOamExt[i].y;
        } else {
            if (oy >= sBottom)
                oy -= 256;
            if (ox >= sRight)
                ox -= 512;
        }
        if (onScreen) {
            int px = ox + (gPortOverlayW - GBA_SCREEN_W) / 2 + 4;
            int py = oy + 6, prio = (a2 >> 10) & 3;
            if (px >= 0 && px < gPortOverlayW && py >= 0 && py < GBA_SCREEN_H) {
                int at = py * gPortOverlayW + px;
                if ((sScreenOccBg[at] == 0 && sScreenOccObj[at] == 0) ||
                    sScreenOccBg[at] < prio || sScreenOccObj[at] < prio * 128 + i)
                    continue;
            }
        }
        if (!onScreen) {
            /* HD glyphs bypass DrawObjs, but must still obey the cartridge's
               background/window and object priority. A covered glyph must
               not be painted over a tutorial or confirmation panel. HUD
               glyphs use their original OAM position for coverage, just as
               PortPpuRenderHud does. Their own docked message window is the
               explicit exception below, keeping field dialogue visible. */
            int px = ox + gPortScreen.originX + 4;
            int py = oy + gPortScreen.originY + 6;
            int prio = (a2 >> 10) & 3;
            if (px >= 0 && px < gPortScreen.width && py >= 0 && py < gPortScreen.height) {
                int at = py * gPortScreen.width + px;
                /* a message window marks its area as covered (it stays in
                   front of the HUD), but the text on it is its own: the
                   field dialogue must stay visible */
                int message = sHudLayer && sMsgMask[at];
                if (!message && ((sOccBg[at] == 0 && sOccObj[at] == 0) || sOccBg[at] < prio ||
                    sOccObj[at] < prio * 128 + i))
                    continue;
            }
        }
        if (onScreen) {
            /* the screen layer: GBA lines 0..159, centred in its width */
            out[n].x = ox + (gPortOverlayW - GBA_SCREEN_W) / 2;
            out[n].y = oy;
        } else if (onHud) {
            int w = gPortHudW, h = gPortHudH;
            int xg = ox - (tag->ax == 2 ? 0 : tag->ax) * gPortScreen.originX, yg = oy - tag->ay * gPortScreen.originY;
            out[n].x = tag->ax == 2 ? HudWorldX(xg, 8, w)
                       : tag->ax < 0 ? xg : (tag->ax > 0 ? w - (GBA_SCREEN_W - xg) : xg + (w - GBA_SCREEN_W) / 2);
            out[n].y = tag->ay < 0 ? yg : (tag->ay > 0 ? h - (GBA_SCREEN_H - yg) - HudRaise() : yg + (h - GBA_SCREEN_H) / 2);
        } else {
            if (ox + 16 <= sLeft || ox >= sRight || oy + 16 <= sTop || oy >= sBottom)
                continue;
            out[n].x = ox + gPortScreen.originX;
            out[n].y = oy + gPortScreen.originY;
        }
        /* colour 1 is the face, colour 2 the shadow, as the game fades them */
        bank = a2 >> 12;
        for (k = 0; k < 2; k++) {
            col[k] = PLTT16[256 + bank * 16 + (tag->style == 2 ? 15 - k : 1 + k)] & 0x7FFF;
            if (bldcnt & 0x10) {
                if (effect == 2)
                    col[k] = Brighten(col[k], evy);
                else if (effect == 3)
                    col[k] = Darken(col[k], evy);
            }
        }
        out[n].code = tag->text;
        out[n].clip0 = out[n].clip1 = 0;
        out[n].style = tag->style;
        out[n].semi = 0;
        if (((a0 >> 10) & 3) == 1) {
            int eva = IO16(0x52) & 31;
            out[n].semi = (uint8_t)(eva >= 1 && eva <= 16 ? eva * 255 / 16 : 0xA0);
        }
        out[n].face = sColorLut[col[0]];
        out[n].shadow = sColorLut[col[1]];
        n++;
    }
    return n;
}

/* HD-2D: 1 where a sprite is what shows, 2 on message windows (from the HUD
   occupancy buffers, filled while PortHd2dActive()); a window hiding OBJs
   reads as 0 / 0. */
void PortPpuSpriteMask(uint8_t* out) {
    int i, n = gPortScreen.width * gPortScreen.height;

    for (i = 0; i < n; i++) {
        uint16_t obj = sOccObj[i];
        uint8_t bg = sOccBg[i];
        out[i] = sMsgMask[i] ? 2 : (obj != 0xFFFFu && !(obj == 0 && bg == 0) && (obj >> 7) <= bg);
    }
}
