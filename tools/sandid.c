/* Sandpile identity on a W x H grid, fast enough for scans and 1024x1024.

   sandid W H [out.raw]   one grid: prints stats, optionally writes W*H height bytes
   sandid scan A B        every square grid n = A..B, one CSV line each
   sandid seam A B        check the odd-grid seam rule for k = A..B (grids 2k and 2k+1)

   CSV columns: n, square, topples, ms, c0, c1, c2, c3
   "square" is the side of the largest centred square made only of 2s. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int64_t stabilize(int32_t *z, int W, int H, int32_t *stack, uint8_t *in) {
    int N = W * H, sp = 0;
    int64_t topples = 0;
    memset(in, 0, N);
    for (int i = 0; i < N; i++) if (z[i] >= 4) { stack[sp++] = i; in[i] = 1; }
    while (sp > 0) {
        int i = stack[--sp];
        in[i] = 0;
        int32_t q = z[i] >> 2;
        if (!q) continue;
        z[i] -= q << 2;
        topples += q;
        int x = i % W, j;
#define PUSH(J) j = (J); z[j] += q; if (z[j] >= 4 && !in[j]) { in[j] = 1; stack[sp++] = j; }
        if (x > 0)     { PUSH(i - 1) }
        if (x < W - 1) { PUSH(i + 1) }
        if (i >= W)    { PUSH(i - W) }
        if (i < N - W) { PUSH(i + W) }
#undef PUSH
    }
    return topples;
}

/* e = stab(6 - stab(6)). Returns total topples; z holds e afterwards. */
static int64_t identity(int32_t *z, int W, int H) {
    int N = W * H;
    int32_t *stack = malloc(sizeof(int32_t) * N);
    uint8_t *in = malloc(N);
    for (int i = 0; i < N; i++) z[i] = 6;
    int64_t t = stabilize(z, W, H, stack, in);
    for (int i = 0; i < N; i++) z[i] = 6 - z[i];
    t += stabilize(z, W, H, stack, in);
    free(stack); free(in);
    return t;
}

/* Largest k (same parity as n) such that the centred k x k block is all 2s. */
static int centre_square(const int32_t *z, int n) {
    int best = 0;
    for (int k = (n % 2 ? 1 : 2); k <= n; k += 2) {
        int lo = (n - k) / 2, hi = lo + k - 1, ok = 1;
        /* only the new ring needs checking; inner block already passed */
        for (int t = lo; t <= hi && ok; t++)
            ok = z[lo * n + t] == 2 && z[hi * n + t] == 2 && z[t * n + lo] == 2 && z[t * n + hi] == 2;
        if (!ok) break;
        best = k;
    }
    return best;
}

static double ms_since(clock_t t0) { return 1000.0 * (clock() - t0) / CLOCKS_PER_SEC; }

/* Seam rule: e(2k+1) with its middle row and column removed equals e(2k), and each
   seam cell is its neighbour minus 1 (the centre: its diagonal neighbour minus 2).
   Counts cells breaking each half: quadrants (*qbad) and seam interior (*sbad),
   and seam cells within 2 of the border (*ebad), where the rule is known to fail. */
static void seam_check(int k, long *qbad, long *sbad, long *ebad) {
    int m = 2 * k, n = m + 1;
    int32_t *ee = malloc(sizeof(int32_t) * m * m), *eo = malloc(sizeof(int32_t) * n * n);
    identity(ee, m, m);
    identity(eo, n, n);
    *qbad = *sbad = *ebad = 0;
    for (int y = 0; y < n; y++)
        for (int x = 0; x < n; x++) {
            int v = eo[y * n + x], want, edge = x < 2 || y < 2 || x > n - 3 || y > n - 3;
            if (y != k && x != k) { *qbad += v != ee[(y - (y > k)) * m + (x - (x > k))]; continue; }
            if (y == k && x == k) want = eo[(k - 1) * n + (k - 1)] - 2;
            else if (y == k) want = eo[(k - 1) * n + x] - 1;
            else want = eo[y * n + (k - 1)] - 1;
            if (edge) *ebad += v != want; else *sbad += v != want;
        }
    free(ee); free(eo);
}

int main(int argc, char **argv) {
    if (argc >= 4 && !strcmp(argv[1], "seam")) {
        int a = atoi(argv[2]), b = atoi(argv[3]);
        printf("k,odd_n,quadrant_bad,seam_interior_bad,seam_edge_bad\n");
        for (int k = a; k <= b; k++) {
            long q, sb, e;
            seam_check(k, &q, &sb, &e);
            printf("%d,%d,%ld,%ld,%ld\n", k, 2 * k + 1, q, sb, e);
            fflush(stdout);
        }
        return 0;
    }
    if (argc >= 4 && !strcmp(argv[1], "scan")) {
        int a = atoi(argv[2]), b = atoi(argv[3]);
        printf("n,square,topples,ms,c0,c1,c2,c3\n");
        for (int n = a; n <= b; n++) {
            int32_t *z = malloc(sizeof(int32_t) * n * n);
            clock_t t0 = clock();
            int64_t t = identity(z, n, n);
            double ms = ms_since(t0);
            long c[4] = {0};
            for (int i = 0; i < n * n; i++) c[z[i]]++;
            printf("%d,%d,%lld,%.0f,%ld,%ld,%ld,%ld\n", n, centre_square(z, n), (long long)t, ms, c[0], c[1], c[2], c[3]);
            fflush(stdout);
            free(z);
        }
        return 0;
    }
    if (argc < 3) { fprintf(stderr, "usage: sandid W H [out.raw] | sandid scan A B\n"); return 1; }
    int W = atoi(argv[1]), H = atoi(argv[2]);
    int32_t *z = malloc(sizeof(int32_t) * W * H);
    clock_t t0 = clock();
    int64_t t = identity(z, W, H);
    long c[4] = {0};
    for (int i = 0; i < W * H; i++) c[z[i]]++;
    printf("%dx%d: %lld topples, %.0f ms, heights %ld %ld %ld %ld", W, H, (long long)t, ms_since(t0), c[0], c[1], c[2], c[3]);
    if (W == H) printf(", centre square %d", centre_square(z, W));
    printf("\n");
    if (argc > 3) {
        FILE *f = fopen(argv[3], "wb");
        for (int i = 0; i < W * H; i++) fputc(z[i], f);
        fclose(f);
    }
    return 0;
}
