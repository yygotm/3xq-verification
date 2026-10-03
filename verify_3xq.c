// 3x+q 写像の計算検証（3xm1/verify2.c を一般化したもの）
// 写像: T(x) = x/2（x 偶数）、(3x+q)/2（x 奇数）。q は奇数で 3 の倍数でないもの（q >= 1、または回帰試験用の q = -1 = 3x-1）。
// 主張: LO <= n < HI の全ての正整数は、引数で与えた最小元 CMINS のいずれかを持つ巡回（既知の巡回）に入る
//       （1 <= n < LO が検証済みであることを前提にする。LO = 1 なら前提なし）。
//       CMINS に無い巡回（または発散）があれば、その最小元の n で FAIL になる（安全側に倒れる）。
//       起動時に CMINS の各元から巡回を辿り、全ての元が最小元以上で元に戻ることを確かめる（偽の最小元は拒否する）。
//
// 帰納法: 各 n（CMINS の元を除く）について、軌道上のある x について
//   (C) x が既知の巡回の元、または
//   (I) x < n、または
//   (P) x の逆向き経路で作る祖先 m = (2^k x + c)/3^a が 1 <= m < n
// を示す。(C) は 3x+q で必要になる: n が自分より大きい最小元の巡回に下から入ることがある（q=5 の 3 → 7 → 13 → 22 → 11 → 19）。
// n が既知の巡回の最大元 CEMAX より大きければ、巡回の元に達した時点で x < n なので (C) は (I) に含まれる。
// よって (C) を判定するのは n <= CEMAX のときだけでよい（その n は遅い経路 trace_ce で 1 つずつ追う）。
// (P) で祖先 m が既知の巡回に入るなら、m の軌道は k 歩で x を通るので、x も既知の巡回に入る（入る点が x の前でも後でも同じ）。(P) は E(y) = 2y（常に T(2y) = y）と O(y) = (2y-q)/3（2y ≡ q mod 3 のとき奇数の整数で T(O(y)) = y）を
// k 回（うち O が a 回）かけたもので、m の軌道は k 歩で x を通る。経路の可否は x mod 3^L だけで決まる（a <= L）。
// q > 0 では c が負になりうるので、祖先が正（m >= 1）であることも確かめる（正なら途中の値も T の前向きの像なので正）。
// 最小の反例 n0 を考えると、(I) でも (P) でも n0 より小さい反例（x または m）が出るので矛盾する。x = n（0 歩目）で (P) なら n を追わずに済む。
//
// 木: 奇数 n を n mod 2^j のクラスに分け、クラスの全員に共通な最初の j 歩を 1 回だけ計算する。
//   クラス（代表 B < 2^j、深さ j）の員は n(t) = B + 2^j t、x_j(t) = e + 3^a t（t は [LO, HI) に入る範囲）。
//   (I)(P) の不等式は t について 1 次なので、範囲の両端で成り立てばクラス全体で成り立つ → クラスごと落とす。
//   (P) は a >= L のときだけ使う（そのとき x_j(t) ≡ e mod 3^L がクラスで一定）。
//   クラスの員数が LEAFN 以下になったら、1 つずつ追う（葉）。
//
// モード: 0 = 本番、1 = 厳密（(P) を使わず、葉では n から素朴に数えた停止時間を記録）、
//         2 = 自己検査（本番の判定を、落とした数・止めた数の全てについて素朴な前向き計算で照合する。小さい範囲用）
//   注: n <= CEMAX の員はどのモードでも trace_ce で (C) を含めて追う（移植元には無い経路）。q=-1 の回帰で stats を丸ごと比べるときは LO > CEMAX にする。
// 使い方: verify_3xq <q> <CMINS> <LO> <HI> <mode> [F L LEAFN [chunk logfile]]
//   CMINS は巡回の最小元のカンマ区切り（例: q=5 なら 1,5,19,23,187,347）。chunk logfile はチェックポイント付き（mode 2・BENCH_STRIDE とは併用不可）
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <errno.h>
#include <unistd.h>                                                 // fsync / fileno（チェックポイントの log。POSIX）

typedef unsigned __int128 u128;
typedef __int128 i128;
#define STEP_CAP 100000
// 確保の失敗は黙って続けない（NULL 参照は未定義動作。検証ツールは止まる方が安全）
static void *xmalloc(size_t n) { void *p = malloc(n); if (!p) { fprintf(stderr, "out of memory (%zu bytes)\n", n); exit(3); } return p; }
static void *xrealloc(void *p, size_t n) { void *q = realloc(p, n); if (!q) { free(p); fprintf(stderr, "out of memory (%zu bytes)\n", n); exit(3); } return q; }
static void *xcalloc(size_t n) { void *p = calloc(n ? n : 1, 1); if (!p) { fprintf(stderr, "out of memory (%zu bytes)\n", n); exit(3); } return p; }

static uint64_t LO, HI;
// 3 進の法はコンパイル時の定数にする（% M3 を掛け算とシフトにするため。実行時の変数だと除算命令になり遅い）
#ifndef LC
#define LC 10
#endif
#if LC == 6
#define M3 729ULL
#elif LC == 8
#define M3 6561ULL
#elif LC == 10
#define M3 59049ULL
#elif LC == 12
#define M3 531441ULL
#else
#error LC must be 6, 8, 10 or 12
#endif
static int MODE, F = 22, L = LC, LEAFN = 2;
// q とその派生値。奇数の一歩は (3x + QP - QN) / 2（QP = max(q,0)、QN = max(-q,0)。符号なし演算のまま書くため）
static int64_t Q; static uint64_t QP, QN, QMOD, Y3;               // QMOD = q mod 3^L、Y3 = 2q mod 3（O が使える y mod 3）
// 巡回の最小元（引数で与える）
#define CM_CAP 256
static uint64_t CM[CM_CAP], CMMAX; static int NCM;
static inline int is_cm(u128 n) { for (int i = 0; i < NCM; i++) if (n == CM[i]) return 1; return 0; }
// 既知の巡回の全ての元（昇順）と最大元。build_ce で CMINS から作る
static uint64_t *CE; static size_t NCE; static uint64_t CEMAX;
static inline int is_ce(u128 x) {
    if (x > CEMAX) return 0;
    uint64_t v = (uint64_t)x; size_t lo = 0, hi = NCE;               // 二分探索
    while (lo < hi) { size_t mid = (lo + hi) / 2; if (CE[mid] < v) lo = mid + 1; else hi = mid; }
    return lo < NCE && CE[lo] == v;
}
static u128 P3[81];
static uint64_t P3M[81], INV2;                                     // 3^a mod 3^L、2 の逆元 mod 3^L
typedef struct { int64_t c; uint8_t a, k; } path_t;
static path_t *ptab;
static uint16_t *pt16; static int64_t *pc;                           // 詰めた表: a | k << 5（0 なら経路なし）と c。判定の頻度が高いので小さくする
static uint64_t P3S[21];
static uint64_t skipbits[(M3 + 63) / 64], SKIP_T;                     // 0 歩目の (P) を剰余だけで決める表と、それが正しくなる n の下限

// ---- 3 進の逆向き経路の表 ----
static double bestR; static path_t bp;
static void pdfs(uint64_t y, int a, int k, int64_t c) {         // y は mod 3^(L-a) で持つ
    double R = pow(3, a) / pow(2, k);
    if (R > bestR) { bestR = R; bp.a = a; bp.k = k; bp.c = c; }
    if (a == L || R * pow(1.5, L - a) <= bestR || k > 40) return;
    uint64_t mod = (uint64_t)P3[L - a];
    if (y % 3 == Y3) {                                              // O(y) = (2y - q)/3 が整数（2y - q ≡ 0 mod 3）
        int64_t v = ((int64_t)(2 * y) - Q) % (int64_t)mod; if (v < 0) v += (int64_t)mod;
        pdfs(((uint64_t)v / 3) % (uint64_t)P3[L - a - 1], a + 1, k + 1, 2 * c - Q * (int64_t)P3[a]);
    }
    pdfs((2 * y) % mod, a, k + 1, 2 * c);
}
static void build_paths(void) {
    for (int i = 0; i <= 80; i++) P3M[i] = (uint64_t)(P3[i] % M3);
    INV2 = (M3 + 1) / 2;
    ptab = xmalloc(sizeof(path_t) * M3);
    for (uint64_t r = 0; r < M3; r++) { bestR = 1; memset(&bp, 0, sizeof bp); pdfs(r, 0, 0, 0); ptab[r] = bp; }
    // class_drops の桁あふれの見積もり（k <= 19、|c| < 2^53）を実際の表で確かめる（起動時に 1 回。外れたら止まる）
    for (uint64_t r = 0; r < M3; r++)
        if (ptab[r].k > 19 || llabs((long long)ptab[r].c) >= (1LL << 53)) {
            fprintf(stderr, "build_paths: r=%llu has k=%d c=%lld (outside the range class_drops assumes)\n", (unsigned long long)r, ptab[r].k, (long long)ptab[r].c); exit(1);
        }
    pt16 = xmalloc(sizeof(uint16_t) * M3); pc = xmalloc(sizeof(int64_t) * M3);
    for (uint64_t r = 0; r < M3; r++) { pt16[r] = ptab[r].a ? (uint16_t)(ptab[r].a | ptab[r].k << 5) : 0; pc[r] = ptab[r].c; }
    for (int i = 0; i <= 20; i++) P3S[i] = (uint64_t)P3[i];
    // 0 歩目の (P): m = (2^k n + c)/3^a。m < n <=> n (3^a - 2^k) > c、m >= 1 <=> 2^k n + c >= 3^a。
    // 3^a > 2^k の経路なら、どちらも n が十分大きければ成り立つ。その下限の最大を SKIP_T とすると、
    // n >= SKIP_T の n では「経路があり 3^a > 2^k」だけで判定できる。
    SKIP_T = 0;
    for (uint64_t r = 0; r < M3; r++) {
        path_t p = ptab[r];
        if (!p.a || P3[p.a] <= ((u128)1 << p.k)) continue;
        int64_t d = (int64_t)(P3[p.a] - ((u128)1 << p.k));
        uint64_t t1 = p.c < 0 ? 1 : (uint64_t)(p.c / d) + 1;                         // m < n
        int64_t need = (int64_t)P3[p.a] - p.c;                                      // 2^k n >= 3^a - c
        uint64_t t2 = need <= 0 ? 1 : (uint64_t)((need + ((int64_t)1 << p.k) - 1) >> p.k);
        uint64_t t = t1 > t2 ? t1 : t2;
        if (t > SKIP_T) SKIP_T = t;
        skipbits[r >> 6] |= (uint64_t)1 << (r & 63);
    }
    fprintf(stderr, "SKIP_T=%llu\n", (unsigned long long)SKIP_T);
}
// (P) の判定: 3^a <= 2^k x + c < 3^a n（x mod 3^L の最良経路。a = 0 は恒等で使わない）
static inline int ptest(u128 x, u128 n, uint64_t xr) {
    uint16_t v = pt16[xr];
    if (!v) return 0;
    uint64_t p3 = P3S[v & 31];
    i128 lhs = (i128)(x << (v >> 5)) + pc[xr], rhs = (i128)((u128)p3 * n);
    return lhs < rhs && lhs >= (i128)p3;
}

// ---- 自己検査用の素朴な計算 ----
static u128 fwd(u128 x, int steps) { while (steps--) x = (x & 1) ? (3 * x + QP - QN) >> 1 : x >> 1; return x; }
static long selfcheck_bad = 0;
static inline void bad(void) {
    #pragma omp atomic
    selfcheck_bad++;
}
// (P) の証明書を照合: m = (2^k x + c)/3^a が正の整数、m < n、m から k 歩で x
static void check_P(u128 x, u128 n) {
    path_t p = ptab[(uint64_t)(x % M3)];
    i128 num = (i128)(x << p.k) + p.c;
    if (!p.a || num < (i128)P3[p.a] || num % (i128)P3[p.a] != 0) { bad(); return; }
    u128 m = (u128)(num / (i128)P3[p.a]);
    if (!(m >= 1 && m < n) || fwd(m, p.k) != x) bad();
}

// CMINS の各元から巡回を辿って CE を作る。元に戻らない・最小元より小さい元が出るなら、その CMINS の元は巡回の最小元ではない（終了）
static int cmp_u64(const void *a, const void *b) { uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y; }
static void build_ce(void) {
    size_t cap = 1024; CE = xmalloc(sizeof(uint64_t) * cap); NCE = 0; CEMAX = 0;
    for (int i = 0; i < NCM; i++) {
        u128 x = CM[i]; long s = 0;
        do {
            if (NCE == cap) { cap *= 2; CE = xrealloc(CE, sizeof(uint64_t) * cap); }
            if (x < CM[i] || (x >> 63)) { fprintf(stderr, "CMINS element %llu is not the minimum of a cycle\n", (unsigned long long)CM[i]); exit(1); }
            CE[NCE++] = (uint64_t)x; if ((uint64_t)x > CEMAX) CEMAX = (uint64_t)x;
            x = (x & 1) ? (3 * x + QP - QN) >> 1 : x >> 1;
            if (++s > STEP_CAP) { fprintf(stderr, "CMINS element %llu does not return within %d steps\n", (unsigned long long)CM[i], STEP_CAP); exit(1); }
        } while (x != CM[i]);
    }
    qsort(CE, NCE, sizeof(uint64_t), cmp_u64);
    for (size_t i = 1; i < NCE; i++) if (CE[i] == CE[i - 1]) { fprintf(stderr, "CMINS elements share a cycle (%llu)\n", (unsigned long long)CE[i]); exit(1); }
    fprintf(stderr, "cycles=%d elements=%zu CEMAX=%llu\n", NCM, NCE, (unsigned long long)CEMAX);
}

typedef struct {
    uint64_t nodes, dropI, dropP, dropn, leafn, skipn, traced, fails, stopP;
    long maxsteps; u128 argmax; int maxdropdepth;
} stats_t;

// 葉の 1 つの n を追う。x は j 歩目の値。戻り値: 停止時の歩数（負なら失敗）
static long trace(u128 n, u128 x, long s, stats_t *st) {
    const u128 lim = (u128)1 << 125;
    u128 nq = n * 32;                    // (P) を試すのは x < 32n のときだけ（それ以上は使える経路がほぼ無い。試さないのは安全側）
    for (;;) {
        if (x < n) return s;
        if (MODE != 1 && x < nq && ptest(x, n, (uint64_t)(x % M3))) { st->stopP++; if (MODE == 2) check_P(x, n); return s; }
        if (x & 1) { if (x > lim) return -2; x = (3 * x + QP - QN) >> 1; } else x >>= 1;
        if (++s > STEP_CAP) return -1;
    }
}
// n <= CEMAX 用の遅い経路: (C) 既知の巡回の元に達した、も止まる条件に加える（厳密モードでも同じ）
static long trace_ce(u128 n, stats_t *st) {
    const u128 lim = (u128)1 << 125;
    u128 x = n, nq = n * 32; long s = 0;
    for (;;) {
        if (is_ce(x) || x < n) return s;
        if (MODE != 1 && x < nq && ptest(x, n, (uint64_t)(x % M3))) { st->stopP++; if (MODE == 2) check_P(x, n); return s; }
        if (x & 1) { if (x > lim) return -2; x = (3 * x + QP - QN) >> 1; } else x >>= 1;
        if (++s > STEP_CAP) return -1;
    }
}

// 64 bit の高速経路（本番用）。奇数のあとの半減は ctz でまとめる（途中の値で判定しないのは安全側）。
// 3x+q が 64 bit を超えそうなら u128 版に渡す。
// k 歩の一括表: x = 2^JK s + u（u = x mod 2^JK）なら T^JK(x) = 3^a(u) s + T^JK(u)（最初の JK 歩の偶奇は u で決まる）。
#ifndef JK
#define JK 10
#endif
#if JK < 1 || JK > 20
#error JK must be 1..20 (3^JK must fit in the uint32 of jt3; 3^21 > 2^32)
#endif
#ifndef TRACE_P
#define TRACE_P 0
#endif
#ifndef LEAF_SKIP
#define LEAF_SKIP 1
#endif
#ifndef TREE_P
#define TREE_P 1
#endif
static uint32_t jt3[1 << JK], jtd[1 << JK];
static void build_jump(void) {
    for (uint64_t u = 0; u < (1u << JK); u++) {
        uint64_t x = u, p = 1;
        for (int i = 0; i < JK; i++) { if (x & 1) { x = (3 * x + QP - QN) >> 1; p *= 3; } else x >>= 1; }
        if (x >> 20) { fprintf(stderr, "build_jump: T^JK(%llu)=%llu >= 2^20 (XLIM assumes d < 2^20)\n", (unsigned long long)u, (unsigned long long)x); exit(1); }
        jt3[u] = (uint32_t)p; jtd[u] = (uint32_t)x;              // q <= 9999 なら T^JK(u) < 1.5^10 (2^10 + q) < 2^20
    }
}
// 本番の葉: JK 歩ずつ進め、区切りごとに (I)(P) を判定する（区切りの間で判定しないのは安全側）。
// 3^JK < 2^16 なので x < 2^47 なら 3^a s + d < 2^64。それを超えたら 1 歩ずつの版に渡す。
static long trace64j(uint64_t n, uint64_t x, long s, stats_t *st);
static long trace64(uint64_t n, uint64_t x, long s, stats_t *st) {
    const uint64_t lim = (UINT64_MAX - QP) / 3;
    uint64_t nq = TRACE_P ? (n < ((uint64_t)1 << 58) ? n * TRACE_P : UINT64_MAX) : 0;
    for (;;) {
        if (x < n) return s;
        if (x < nq && ptest(x, n, x % M3)) { st->stopP++; if (MODE == 2) check_P(x, n); return s; }
        if (x & 1) { if (x > lim) return trace(n, x, s, st); x = 3 * x + QP - QN; }
        int z = __builtin_ctzll(x); x >>= z; s += z;
        if (s > STEP_CAP) return -1;
        if (x < ((uint64_t)1 << 47)) return trace64j(n, x, s, st);
    }
}
static long trace64j(uint64_t n, uint64_t x, long s, stats_t *st) {
    uint64_t nq = TRACE_P ? (n < ((uint64_t)1 << 58) ? n * TRACE_P : UINT64_MAX) : 0;   // 追う途中の (P)。実測では無し（0）が最速
    for (;;) {
        if (x < n) return s;
        if (x < nq && ptest(x, n, x % M3)) { st->stopP++; if (MODE == 2) check_P(x, n); return s; }
        if (x >= ((uint64_t)1 << 47)) return trace64(n, x, s, st);
        uint32_t u = x & ((1u << JK) - 1);
        x = (uint64_t)jt3[u] * (x >> JK) + jtd[u]; s += JK;
        if (s > STEP_CAP) return -1;
    }
}

// ---- 葉の数をまとめて追う（本番と自己検査）: 員を行列に貯め、W 本の軌道を交互に JK 歩ずつ進める ----
// 止まる判定（x < n）と入れ替えは条件付き移動で書き、分岐の予測外れと依存の待ちを減らす。
// x が XLIM 以上になる・歩数が上限に達するのは稀なので、その軌道だけ 1 本ずつの版（trace）に回す。
#ifndef W
#define W 8
#endif
// ビルド条件の文字列（起動時の表示とチェックポイントの tag に入れる。別ビルドが書いた DONE 行を済んだことにしないため）
#ifndef SRC_HASH
#define SRC_HASH "nohash"                                             // 本番は -DSRC_HASH=\"$(md5sum verify_3xq.c | cut -c1-12)\" で渡す
#endif
#ifdef NO_CM_EXCL
#define CM_EXCL 0
#else
#define CM_EXCL 1
#endif
#define STR_(x) #x
#define STR(x) STR_(x)
#define BUILD_STR "jk" STR(JK) ",w" STR(W) ",tp" STR(TREE_P) ",ls" STR(LEAF_SKIP) ",trp" STR(TRACE_P) ",sc" STR(STEP_CAP) ",cmx" STR(CM_EXCL) ",src=" SRC_HASH
#define QCAP 1024
#define XLIM ((uint64_t)1 << (63 - (JK * 585 + 999) / 1000))     // x < XLIM なら 3^JK (x >> JK) + d < 2^64（log2 3 - 1 < 0.585。JK=10 で 2^57。d < 2^20 を含めても収まる）
typedef struct { uint64_t n, x; uint32_t j; } item_t;
static __thread item_t Qu[QCAP + 1];
static __thread size_t qn;
static void slow_one(uint64_t n, u128 x, long s, stats_t *st) {       // 稀な場合: 1 本ずつの版で最後まで追う
    long r = trace(n, x, s, st);
    if (r < 0) {
        st->fails++;
        #pragma omp critical
        fprintf(stderr, "FAIL n=%llu code=%ld\n", (unsigned long long)n, r);
    } else if (r > st->maxsteps) { st->maxsteps = r; st->argmax = n; }
}
static void kernel(stats_t *st) {
    size_t m = qn, next = 0, left = m;
    if (!m) return;
    Qu[m] = (item_t){UINT64_MAX, 0, 0};                                 // 番兵: 0 < n で即座に終わる
    uint64_t n[W], x[W]; uint32_t sj[W], jj[W];
    for (int w = 0; w < W; w++) { n[w] = UINT64_MAX; x[w] = 0; sj[w] = 0; jj[w] = 0; }
    long ms = st->maxsteps; u128 am = st->argmax;
    while (left) {
        #pragma GCC unroll 16
        for (int w = 0; w < W; w++) {
            uint64_t xv = x[w], nv = n[w];
            int done = xv < nv, real = nv != UINT64_MAX, fin = done & real;
            left -= fin;
            long steps = (long)jj[w] + (long)JK * sj[w];
            if (fin && steps > ms) { ms = steps; am = nv; }
            if (MODE == 2 && fin && fwd(nv, (int)steps) != xv) bad();   // 止まった値を素朴な前向き計算で照合
            size_t i = next < m ? next : m;
            item_t it = Qu[i];
            next += done & (next < m);
            uint32_t u = xv & ((1u << JK) - 1);
            uint64_t xj = (uint64_t)jt3[u] * (xv >> JK) + jtd[u];
            uint32_t s2 = sj[w] + 1;
            x[w] = done ? it.x : xj; n[w] = done ? it.n : nv; sj[w] = done ? 0 : s2; jj[w] = done ? it.j : jj[w];
            if (__builtin_expect(!done && (xj >= XLIM || s2 > STEP_CAP / JK), 0)) {
                slow_one(nv, xj, (long)jj[w] + (long)JK * s2, st);       // この軌道は 1 本ずつの版で終える
                left--;
                n[w] = UINT64_MAX; x[w] = 0;                              // 番兵に戻す（次の周で補充）
            }
        }
    }
    if (ms > st->maxsteps) { st->maxsteps = ms; st->argmax = am; }
    qn = 0;
}

// 本番用の葉（64 bit の足し算だけ）。条件: 員が既知の巡回の元を含まない（n0 > CEMAX。CEMAX >= CMMAX なので最小元も含まない）、飛ばす判定が剰余だけで決まる（n0 >= SKIP_T）、
// 員の n と x が 2^63 未満（n は HI < 2^62 で常に、x は呼び出し側で x1 を確認）。判定の中身は leaf() の一般経路と同じ。
static void leaf_fast(uint64_t n, uint64_t dn, uint64_t x, uint64_t dx, uint64_t r, uint64_t dr, uint64_t cnt, int j, stats_t *st) {
    uint64_t skipped = 0, q = qn;
    for (uint64_t t = 0; t < cnt; t++) {
        int skip = LEAF_SKIP & (int)((skipbits[r >> 6] >> (r & 63)) & 1);
        skipped += skip;
        if (__builtin_expect(!skip && x >= XLIM, 0)) slow_one(n, x, j, st);   // 稀: u128 の 1 歩版へ
        else {
            Qu[q] = (item_t){n, x, (uint32_t)j};                           // 分岐なしで追加（飛ばすなら q を進めない）
            q += !skip;
            if (q == QCAP) { qn = q; kernel(st); q = 0; }
        }
        n += dn; x += dx; r += dr; r -= r >= M3 ? M3 : 0;
    }
    qn = q;
    st->leafn += cnt; st->skipn += skipped; st->traced += cnt - skipped;
}

static void leaf(uint64_t B, int j, int a, u128 e, uint64_t tlo, uint64_t thi, stats_t *st) {
    // 員を t の順に足し算で進める: n += 2^j、x += 3^a、n mod 3^L += 2^j mod 3^L
    u128 n = (u128)B + ((u128)tlo << j), x = e + P3[a] * tlo, dx = P3[a];
    uint64_t rn = (uint64_t)(n % M3), dr = (uint64_t)((((u128)1) << j) % M3), dn = (uint64_t)1 << j;
    if (MODE == 0 && n > CEMAX && n >= SKIP_T && !((x + dx * (thi - tlo - 1)) >> 63)) {
        leaf_fast((uint64_t)n, dn, (uint64_t)x, (uint64_t)dx, rn, dr, thi - tlo, j, st);
        return;
    }
    for (uint64_t t = tlo; t < thi; t++, n += dn, x += dx, rn = rn + dr >= M3 ? rn + dr - M3 : rn + dr) {
        st->leafn++;
        if (is_cm(n)) continue;
        long s;
        if (n <= CEMAX) {
            s = trace_ce(n, st);                                      // 小さい n: (C) も含めて 1 つずつ（行列には入れない）
        } else if (MODE == 1) {
            s = trace(n, n, 0, st);                                   // 厳密: n から素朴に
        } else {
            if (MODE == 2 && fwd(n, j) != x) bad();                  // x_j の公式を照合
            uint64_t r = rn;                                         // 0 歩目で (P): n を飛ばす
            if (MODE == 2 && r != (uint64_t)(n % M3)) bad();
            int skip;
            if (n >= SKIP_T) skip = (skipbits[r >> 6] >> (r & 63)) & 1;   // n が大きければ剰余だけで決まる（ビット表、L1 に収まる）
            else skip = ptest(n, n, r);                              // 小さい n は厳密に（正値条件も含む）
            skip &= LEAF_SKIP;
            st->skipn += skip;
            if (MODE == 2 && skip) check_P(n, n);
            if (__builtin_expect(!skip && x >= XLIM, 0)) { st->traced++; slow_one((uint64_t)n, x, j, st); continue; }
            Qu[qn] = (item_t){(uint64_t)n, (uint64_t)x, (uint32_t)j};  // 分岐なしで追加（飛ばすなら qn を進めない）
            qn += !skip; st->traced += !skip;
            if (qn == QCAP) kernel(st);
            continue;
        }
        st->traced++;
        if (s < 0) {
            st->fails++;
            #pragma omp critical
            fprintf(stderr, "FAIL n=%llu code=%ld\n", (unsigned long long)n, s);
        } else if (s > st->maxsteps) { st->maxsteps = s; st->argmax = n; }
    }
}

static inline void trange(uint64_t B, int j, uint64_t *tlo, uint64_t *thi) {
    uint64_t w = (uint64_t)1 << j;
    *tlo = LO > B ? (LO - B + w - 1) >> j : 0;
    *thi = HI > B ? (HI - B + w - 1) >> j : 0;
}

// クラスの判定: 1 = (I) で落ちる、2 = (P) で落ちる、0 = 落ちない
// 両端で十分な根拠: 員は n(t) = B + 2^j t、x(t) = e + 3^a t（t = tlo..t1 の整数）で、どちらも t の 1 次式。
//   (I) d(t) = x(t) − n(t) は 1 次式。1 次式の値は区間の両端の値の凸結合なので、両端で負なら間の全ての t で負。
//   (P) 3^a' n(t) − (2^k x(t) + c) と 2^k x(t) + c − 3^a' も t の 1 次式（a', k, c は経路の定数）なので同じ。経路は x mod 3^L で決まり、
//       a >= L なら x(t) ≡ e (mod 3^L) がクラスで一定なので全ての t で同じ経路が使え、祖先 (2^k x(t) + c)/3^a' は整数。
static int class_drops(uint64_t B, int j, int a, u128 e, uint64_t r, uint64_t tlo, uint64_t thi) {
    uint64_t t1 = thi - 1;
    u128 n0 = (u128)B + ((u128)tlo << j), n1 = (u128)B + ((u128)t1 << j);
    u128 x0 = e + P3[a] * tlo, x1 = e + P3[a] * t1;
    // 桁あふれを避ける（落とさないのは安全側）。表に記録される経路（a', k, c）は R = 3^a'/2^k > 1 を満たすので
    // k < a'·log2 3 <= LC·1.585: LC=12 で k <= 19。|c| <= |q|·3^a'·2^k < 2^14·2^20·2^19 < 2^53。
    // x1 < 2^90 なら x << k < 2^109、3^a' n < 3^12 · 2^62 < 2^82 で、どれも i128 に収まる。LC を上げるときはここを見直す。
    if (x1 >> 90) return 0;
    int d = 0;
    if (x0 < n0 && x1 < n1) d = 1;
    else if (TREE_P && MODE != 1 && a >= L && ptest(x0, n0, r) && ptest(x1, n1, r)) d = 2;
    if (!d) return 0;
    // 巡回の最小元 cm を含むクラスは落とさず葉まで下ろす（葉では追わずに飛ばす）。冗長な安全策で、落としても正しさは崩れない（一般の q で）:
    //   (I) 落ちるなら全ての t で x(t) < n(t) だが、n(t*) = cm なら x(t*) = T^j(cm) は cm の巡回の元で cm 以上。矛盾するので (I) では落ちない。
    //   (P) 落ちるなら m' = (2^k x(t*) + c)/3^a' が正整数で 1 <= m' < cm、m' から k 歩で T^j(cm) に着く。cm の巡回は既知なので
    //       これは「cm は既知の巡回に入る」の正しい証明書。落としても誤りではない。
    // 判定の後ろに置くのは、落とすと決まった節でだけ確かめれば足りるから（返す値は前に置いた場合と同じ。n0 > CMMAX なら含みようがない）。
    // -DNO_CM_EXCL はこの除外を外した変異（試験用。本番では定義しない。tag の cmx で区別できる）。
#ifndef NO_CM_EXCL
    if (n0 <= CMMAX) {
        uint64_t mask = ((uint64_t)1 << j) - 1;
        for (int i = 0; i < NCM; i++) {
            uint64_t cm = CM[i];
            if (cm >= n0 && cm <= n1 && ((cm - B) & mask) == 0) return 0;
        }
    }
#endif
    return d;
}

// 奇数の一歩の剰余: (3 rc + q) / 2 mod 3^L
static inline uint64_t r_odd(uint64_t rc) { return (3 * rc + QMOD) % M3 * INV2 % M3; }

static void dfs(uint64_t B, int j, int a, u128 e, uint64_t r, stats_t *st) {
    uint64_t tlo, thi;
    trange(B, j, &tlo, &thi);
    if (tlo >= thi) return;
    st->nodes++;
    if (MODE == 2 && e % M3 != r) bad();                               // 持ち回りの剰余を照合
    int d = class_drops(B, j, a, e, r, tlo, thi);
    if (d) {
        uint64_t cnt = thi - tlo;
        if (d == 1) st->dropI += cnt; else st->dropP += cnt;
        if (j > st->maxdropdepth) st->maxdropdepth = j;
        if (MODE == 2)                                               // 落としたクラスの全員を素朴に照合
            for (uint64_t t = tlo; t < thi; t++) {
                u128 n = (u128)B + ((u128)t << j), x = fwd(n, j);
                if (x != e + P3[a] * t) { bad(); continue; }
                if (d == 1) { if (!(x < n)) bad(); } else check_P(x, n);
            }
        return;
    }
    if (thi - tlo <= (uint64_t)LEAFN || j >= 62 || (e >> 90)) { leaf(B, j, a, e, tlo, thi, st); return; }
    for (int b = 0; b < 2; b++) {
        uint64_t B2 = B + ((uint64_t)b << j), rc = b ? (r + P3M[a]) % M3 : r, r2;
        u128 ec = b ? e + P3[a] : e, e2; int a2 = a;
        if (ec & 1) { e2 = (3 * ec + QP - QN) >> 1; a2++; r2 = r_odd(rc); } else { e2 = ec >> 1; r2 = rc * INV2 % M3; }
        dfs(B2, j + 1, a2, e2, r2, st);
    }
}

// ---- 分割（並列化とチェックポイントの単位）: 深さ F まで下ろしたクラスの列 ----
typedef struct { uint64_t B; int j, a; u128 e; uint64_t r; } node_t;
static node_t *front; static size_t nfront, capfront;
static stats_t pre;                                                  // 分割の途中で落ちた・葉になったもの
static void push_front(node_t nd) {                                  // realloc はここだけ（失敗は xrealloc が止める）
    if (nfront == capfront) { capfront = capfront ? 2 * capfront : 1024; front = xrealloc(front, sizeof(node_t) * capfront); }
    front[nfront++] = nd;
}
static void split(uint64_t B, int j, int a, u128 e, uint64_t r) {
    uint64_t tlo, thi;
    trange(B, j, &tlo, &thi);
    if (tlo >= thi) return;
    if (j == F || thi - tlo <= (uint64_t)LEAFN) { push_front((node_t){B, j, a, e, r}); return; }
    pre.nodes++;
    int d = class_drops(B, j, a, e, r, tlo, thi);
    if (d) {                                                         // 浅い段で落ちるクラス（自己検査は dfs 側と同じ手順を踏むため、ここでは front に回す）
        if (MODE == 2) { push_front((node_t){B, j, a, e, r}); pre.nodes--; return; }
        if (d == 1) pre.dropI += thi - tlo; else pre.dropP += thi - tlo;
        return;
    }
    for (int b = 0; b < 2; b++) {
        uint64_t B2 = B + ((uint64_t)b << j), rc = b ? (r + P3M[a]) % M3 : r, r2;
        u128 ec = b ? e + P3[a] : e, e2; int a2 = a;
        if (ec & 1) { e2 = (3 * ec + QP - QN) >> 1; a2++; r2 = r_odd(rc); } else { e2 = ec >> 1; r2 = rc * INV2 % M3; }
        split(B2, j + 1, a2, e2, r2);
    }
}

static void add(stats_t *s, const stats_t *t) {
    s->nodes += t->nodes; s->dropI += t->dropI; s->dropP += t->dropP; s->leafn += t->leafn; s->skipn += t->skipn;
    s->traced += t->traced; s->fails += t->fails; s->stopP += t->stopP;
    if (t->maxsteps > s->maxsteps) { s->maxsteps = t->maxsteps; s->argmax = t->argmax; }
    if (t->maxdropdepth > s->maxdropdepth) s->maxdropdepth = t->maxdropdepth;
}

static size_t STRIDE = 1;                                            // ベンチマーク用の抜き取り（環境変数 BENCH_STRIDE）。本番は 1
static stats_t run_front(size_t i0, size_t i1) {
    stats_t tot = {0};
    #pragma omp parallel
    {
        stats_t st = {0};
        #pragma omp for schedule(dynamic, 1) nowait
        for (size_t i = i0; i < i1; i += STRIDE) dfs(front[i].B, front[i].j, front[i].a, front[i].e, front[i].r, &st);
        kernel(&st);                                                     // 行列に残った分を追う
        #pragma omp critical
        add(&tot, &st);
    }
    return tot;
}

static void print_stats(FILE *o, const stats_t *s, double dt, double span) {
    fprintf(o, "nodes=%llu dropI=%llu dropP=%llu leafn=%llu skipn=%llu traced=%llu stopP=%llu fails=%llu maxsteps=%ld at n=%llu maxdropdepth=%d time=%.3fs rate=%.3e n/s\n",
            (unsigned long long)s->nodes, (unsigned long long)s->dropI, (unsigned long long)s->dropP, (unsigned long long)s->leafn,
            (unsigned long long)s->skipn, (unsigned long long)s->traced, (unsigned long long)s->stopP, (unsigned long long)s->fails,
            s->maxsteps, (unsigned long long)s->argmax, s->maxdropdepth, dt, span / dt);
}

static uint64_t parse_u64(const char *s, uint64_t lo, uint64_t hi, const char *name) {   // 範囲付きの厳密な整数解析（失敗は終了）
    char *end; errno = 0;
    unsigned long long v = strtoull(s, &end, 10);
    // strtoull は先頭の空白・'+'・'-' を受け付け、"-1" を 2^64 − 1 にする。先頭が数字でなければ拒否する
    if (*s < '0' || *s > '9' || errno || end == s || *end || v < lo || v > hi) {
        fprintf(stderr, "bad %s: '%s' (allowed %llu..%llu)\n", name, s, (unsigned long long)lo, (unsigned long long)hi); exit(1);
    }
    return (uint64_t)v;
}
// q の解析: "-1" か、1..9999 の奇数で 3 の倍数でないもの（q <= -3 は正の整数の上で閉じないので受け付けない）
static int64_t parse_q(const char *s) {
    if (strcmp(s, "-1") == 0) return -1;
    int64_t v = (int64_t)parse_u64(s, 1, 9999, "q");
    if (v % 2 == 0 || v % 3 == 0) { fprintf(stderr, "bad q: %s (must be odd and not divisible by 3)\n", s); exit(1); }
    return v;
}
// 巡回の最小元の解析: カンマ区切りの正の整数（重複は拒否）
static void parse_cm(const char *s) {
    char buf[4096];
    if (strlen(s) >= sizeof buf) { fprintf(stderr, "CMINS too long\n"); exit(1); }
    // strtok は空の要素（",," と先頭・末尾の ","）を黙って読み飛ばす。tag には argv[2] がそのまま入るので、表記揺れは受け付けない
    { size_t n = strlen(s);
      if (n == 0 || s[0] == ',' || s[n - 1] == ',' || strstr(s, ",,")) { fprintf(stderr, "bad CMINS: '%s' (empty element)\n", s); exit(1); } }
    strcpy(buf, s);
    NCM = 0; CMMAX = 0;
    for (char *tok = strtok(buf, ","); tok; tok = strtok(NULL, ",")) {
        if (NCM == CM_CAP) { fprintf(stderr, "too many CMINS (max %d)\n", CM_CAP); exit(1); }
        uint64_t v = parse_u64(tok, 1, ((uint64_t)1 << 62) - 1, "CMINS element");
        for (int i = 0; i < NCM; i++) if (CM[i] == v) { fprintf(stderr, "duplicate CMINS element %llu\n", (unsigned long long)v); exit(1); }
        CM[NCM++] = v; if (v > CMMAX) CMMAX = v;
    }
    if (!NCM) { fprintf(stderr, "CMINS empty\n"); exit(1); }
}
// DONE 行の解析: この実行の tag と区画割りに合う行だけ受け付け、区画番号と統計を返す（再開の判定と最終集計で共用）
typedef struct { uint64_t dropI, dropP, leafn, fails; long maxsteps; unsigned long long argmax; } donestat_t;
#define TAGCAP 4608                                                   // tag の上限（CMINS 4095 + 固定部 + ビルド条件）。下の %4607 と合わせる
static int parse_done(const char *line, const char *tag, size_t chunk, size_t nfront, const uint64_t *expect, size_t *ci, donestat_t *d) {
    unsigned long long x, y; char t2[TAGCAP]; int off = 0;
    size_t len = strlen(line);                                        // 書きかけの行（末尾が欠けた・改行が無い）は受け付けない
    if (len < 5 || strcmp(line + len - 5, " n/s\n") != 0) return 0;
    if (sscanf(line, "DONE %llu %llu %4607[^|]|%n", &x, &y, t2, &off) < 3 || off == 0 || strcmp(t2, tag) != 0) return 0;
    if (x % chunk != 0 || x >= nfront || y != (x + chunk < nfront ? x + chunk : nfront)) return 0;
    unsigned long long dI, dP, lf, fl, am; long ms;
    if (sscanf(line + off, " nodes=%*u dropI=%llu dropP=%llu leafn=%llu skipn=%*u traced=%*u stopP=%*u fails=%llu maxsteps=%ld at n=%llu",
               &dI, &dP, &lf, &fl, &ms, &am) != 6) return 0;
    if (dI + dP + lf != expect[x / chunk]) return 0;                  // 区画ごとの件数も照合（合計だけでは区画間の相殺を見逃す）
    *ci = (size_t)(x / chunk); d->dropI = dI; d->dropP = dP; d->leafn = lf; d->fails = fl; d->maxsteps = ms; d->argmax = am;
    return 1;
}

int main(int argc, char **argv) {
    // 引数は 5〜8 個（単発）か 10 個（チェックポイント付き）。9 個（logfile の書き忘れ）や 11 個以上は黙って単発にせず拒否する
    if (argc < 6 || argc == 10 || argc > 11) { fprintf(stderr, "usage: verify_3xq q CMINS LO HI mode [F L LEAFN [chunk logfile]]\n"); return 1; }
    Q = parse_q(argv[1]);
    QP = Q > 0 ? (uint64_t)Q : 0; QN = Q < 0 ? (uint64_t)(-Q) : 0;
    QMOD = (uint64_t)(((Q % (int64_t)M3) + (int64_t)M3) % (int64_t)M3);
    Y3 = (uint64_t)((((2 * Q) % 3) + 3) % 3);
    parse_cm(argv[2]);
    build_ce();
    const uint64_t HMAX = ((uint64_t)1 << 62) - 1;                    // HI < 2^62: n < 2^62 で 32n・3^12 n・(3/2)^62 n が u128 に収まる前提
    LO = parse_u64(argv[3], 1, HMAX - 1, "LO"); HI = parse_u64(argv[4], LO + 1, HMAX, "HI");
    MODE = (int)parse_u64(argv[5], 0, 2, "mode");
    if (argc > 6) F = (int)parse_u64(argv[6], 1, 40, "F");
    if (argc > 7) L = (int)parse_u64(argv[7], LC, LC, "L");            // L はコンパイル時定数 LC と一致しなければならない
    if (argc > 8) LEAFN = (int)parse_u64(argv[8], 1, 1 << 30, "LEAFN");
    if (getenv("BENCH_STRIDE")) STRIDE = (size_t)parse_u64(getenv("BENCH_STRIDE"), 1, (uint64_t)1 << 30, "BENCH_STRIDE");
    size_t chunk = 0; const char *logf = NULL;
    if (argc == 11) {
        chunk = (size_t)parse_u64(argv[9], 1, SIZE_MAX, "chunk"); logf = argv[10];
        // 自己検査の不一致（selfcheck_bad）はチェックポイントの log に残らない。抜き取りは区画の統計を歪める。どちらも単発でだけ使う
        if (MODE == 2) { fprintf(stderr, "mode 2 (selfcheck) cannot be used with chunk/logfile\n"); return 1; }
        if (STRIDE > 1) { fprintf(stderr, "BENCH_STRIDE cannot be used with chunk/logfile\n"); return 1; }
        FILE *lf = fopen(logf, "a");                                 // 先に log を作る（区画が 0 個でも最後の読み込みで落ちない。パスの誤りも準備の前に分かる）
        if (!lf) { perror(logf); return 3; }
        fclose(lf);
    }
    P3[0] = 1; for (int i = 1; i <= 80; i++) P3[i] = 3 * P3[i - 1];
    struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
    build_paths();
    build_jump();
    // 根: 奇数 n = 1 + 2t、x_1 = T(1 + 2t) = (3 + q)/2 + 3t（深さ 1、a = 1、代表 B = 1）。偶数 n は 1 歩で n/2 < n。
    u128 e1 = (u128)((3 + Q) / 2);
    split(1, 1, 1, e1, (uint64_t)(e1 % M3));
    clock_gettime(CLOCK_MONOTONIC, &t1);
    fprintf(stderr, "q=%lld ncm=%d cmmax=%llu LO=%llu HI=%llu mode=%d F=%d L=%d LEAFN=%d front=%zu build=%s setup=%.2fs\n", (long long)Q, NCM,
            (unsigned long long)CMMAX, (unsigned long long)LO, (unsigned long long)HI, MODE, F, L, LEAFN, nfront, BUILD_STR,
            (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec));
    double span = (double)(HI - LO);
    if (getenv("BENCH_STRIDE")) { span /= STRIDE; fprintf(stderr, "BENCH: every %zu-th of the split only, rate scaled\n", STRIDE); }
    if (argc < 11) {
        clock_gettime(CLOCK_MONOTONIC, &t0);
        stats_t s = run_front(0, nfront); add(&s, &pre);
        clock_gettime(CLOCK_MONOTONIC, &t1);
        double dt = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
        uint64_t odd = HI / 2 - LO / 2;                                  // [LO, HI) の奇数の個数
        print_stats(stdout, &s, dt, span);
        if (STRIDE == 1) printf("odd in range=%llu accounted(dropI+dropP+leafn)=%llu %s\n", (unsigned long long)odd,
               (unsigned long long)(s.dropI + s.dropP + s.leafn), odd == s.dropI + s.dropP + s.leafn ? "OK" : "MISMATCH");
        if (MODE == 2) printf("selfcheck_bad=%ld\n", selfcheck_bad);
        if (s.fails || selfcheck_bad || (STRIDE == 1 && odd != s.dropI + s.dropP + s.leafn)) return 2;
        if (STRIDE > 1) { fprintf(stderr, "BENCH run (every %zu-th of the split): NOT a verification, exit 4\n", STRIDE); return 4; }   // 抜き取りを「検証済み」に見せない
        return 0;
    }
    // チェックポイント付き: 分割の列を chunk 個ずつ実行し、済んだものを log に追記する
    size_t nch = nfront / chunk + (nfront % chunk != 0);
    char *done = xcalloc(nch);
    uint64_t *expect = xcalloc(sizeof(uint64_t) * nch);               // 区画ごとの奇数の個数（front の各節の員数の和。dfs の dropI+dropP+leafn と一致するはず）
    for (size_t i = 0; i < nfront; i++) { uint64_t tlo, thi; trange(front[i].B, front[i].j, &tlo, &thi); expect[i / chunk] += thi - tlo; }
    char tag[TAGCAP];
    // tag にはビルド条件とソースの版（BUILD_STR）も入れる: 別のビルド・修正前の版が書いた DONE 行を再開でも ALLDONE でも受け付けない
    int tl = snprintf(tag, sizeof tag, "q=%lld CMINS=%s LO=%llu HI=%llu mode=%d F=%d L=%d LEAFN=%d nfront=%zu build=%s", (long long)Q, argv[2],
             (unsigned long long)LO, (unsigned long long)HI, MODE, F, L, LEAFN, nfront, BUILD_STR);
    if (tl < 0 || (size_t)tl >= sizeof tag) { fprintf(stderr, "tag too long (%d >= %zu)\n", tl, sizeof tag); return 1; }   // 切り詰めた tag は衝突しうる
    FILE *lf = fopen(logf, "r");
    if (!lf && errno != ENOENT) { perror(logf); return 3; }           // 「無い」以外の失敗で log を無視しない
    if (lf) {
        char line[8192]; size_t ci; donestat_t d;
        while (fgets(line, sizeof line, lf)) if (parse_done(line, tag, chunk, nfront, expect, &ci, &d)) done[ci] = 1;
        fclose(lf);
    }
    for (size_t c = 0; c < nch; c++) {
        if (done[c]) continue;
        size_t i0 = c * chunk, i1 = i0 + chunk < nfront ? i0 + chunk : nfront;
        clock_gettime(CLOCK_MONOTONIC, &t0);
        stats_t s = run_front(i0, i1);
        clock_gettime(CLOCK_MONOTONIC, &t1);
        double dt = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
        lf = fopen(logf, "a+");                                      // a+: 末尾を読める（書き込みは常に末尾）
        if (!lf) { perror(logf); return 3; }
        {   // 前回の書きかけの行（改行なし）に連結しないよう、末尾が '\n' でなければ先に改行を書く
            int last = '\n';
            if (fseek(lf, 0, SEEK_END) == 0 && ftell(lf) > 0 && fseek(lf, -1, SEEK_END) == 0) last = fgetc(lf);
            fseek(lf, 0, SEEK_END);                                   // 読みから書きに移る前に位置決め（C の規則）
            if (last != '\n') fputc('\n', lf);
        }
        fprintf(lf, "%s %zu %zu %s| ", s.fails ? "FAIL" : "DONE", i0, i1, tag);
        print_stats(lf, &s, dt, span * (i1 - i0) / nfront);
        int werr = fflush(lf) != 0 || ferror(lf); werr |= fsync(fileno(lf)) != 0; werr |= fclose(lf) != 0;   // 書けなかった区画を済んだことにしない。fsync で電源断でも DONE 行を残す
        if (werr) { perror(logf); return 3; }
        if (s.fails) return 2;
    }
    // 全区画が済んだ: log の DONE 行（再開前の分も含む）から合計を作り、奇数の個数と照合する
    stats_t all = pre; memset(done, 0, nch);
    lf = fopen(logf, "r"); if (!lf) { perror(logf); return 3; }
    { char line[8192]; size_t ci; donestat_t d;
      while (fgets(line, sizeof line, lf))
          if (parse_done(line, tag, chunk, nfront, expect, &ci, &d) && !done[ci]) {
              done[ci] = 1; all.dropI += d.dropI; all.dropP += d.dropP; all.leafn += d.leafn; all.fails += d.fails;
              if (d.maxsteps > all.maxsteps) { all.maxsteps = d.maxsteps; all.argmax = d.argmax; }
          } }
    fclose(lf);
    size_t nseen = 0; for (size_t c = 0; c < nch; c++) nseen += done[c];
    uint64_t odd = HI / 2 - LO / 2, acc = all.dropI + all.dropP + all.leafn;
    int ok = nseen == nch && acc == odd && all.fails == 0;
    lf = fopen(logf, "a"); if (!lf) { perror(logf); return 3; }
    // 照合に落ちたら行頭を ALLDONE にしない（grep ^ALLDONE で完了と読まれないように）
    fprintf(lf, "%s %s| chunks=%zu/%zu odd=%llu accounted=%llu %s maxsteps=%ld at n=%llu | pre: ", ok ? "ALLDONE" : "ALLFAIL", tag, nseen, nch,
            (unsigned long long)odd, (unsigned long long)acc, ok ? "OK" : "MISMATCH", all.maxsteps, (unsigned long long)all.argmax);
    print_stats(lf, &pre, 0, 0);
    { int werr = ferror(lf); werr |= fclose(lf) != 0; if (werr) { perror(logf); return 3; } }
    free(done); free(expect);
    return ok ? 0 : 2;
}
