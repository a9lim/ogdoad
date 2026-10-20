/* gf2x_mul replacement: additive-FFT (bitpolymul2) above a threshold, gf2x below.
 * Link with a copy of libgf2x.a whose gf2x_mul was renamed to gf2x_mul_orig. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern int gf2x_mul_orig(unsigned long *c, const unsigned long *a, unsigned long sa, const unsigned long *b, unsigned long sb);
extern void bitpolymul_2_64(uint64_t *c, const uint64_t *a, const uint64_t *b, unsigned n_64);
static long bpm_T = -1;
static void bpm_eq(uint64_t *c, const uint64_t *a, unsigned long sa, const uint64_t *b, unsigned long sb, unsigned long n) {
    /* c[0..sa+sb) = a*b where sa,sb <= n; uses one length-n call */
    uint64_t *A = calloc(n, 8), *B = calloc(n, 8), *C = malloc(2 * n * 8);
    memcpy(A, a, sa * 8); memcpy(B, b, sb * 8);
    bitpolymul_2_64(C, A, B, (unsigned)n);
    memcpy(c, C, (sa + sb) * 8);
    free(A); free(B); free(C);
}
int gf2x_mul(unsigned long *c, const unsigned long *a, unsigned long sa, const unsigned long *b, unsigned long sb) {
    if (bpm_T < 0) { const char *e = getenv("BPM_THRESHOLD"); bpm_T = e ? atol(e) : 3000; }
    unsigned long mn = sa < sb ? sa : sb, mx = sa < sb ? sb : sa;
    if ((long)mn < bpm_T || bpm_T == 0) return gf2x_mul_orig(c, a, sa, b, sb);
    if (mx <= 2 * mn) { bpm_eq((uint64_t*)c, (const uint64_t*)a, sa, (const uint64_t*)b, sb, mx); return 0; }
    /* unbalanced: chunk the longer operand into pieces of length mn */
    const uint64_t *L = (const uint64_t*)(sa >= sb ? a : b), *S = (const uint64_t*)(sa >= sb ? b : a);
    uint64_t *acc = calloc(mx + mn + mn, 8), *tmp = malloc(2 * mn * 8);
    for (unsigned long off = 0; off < mx; off += mn) {
        unsigned long len = mx - off < mn ? mx - off : mn;
        bpm_eq(tmp, L + off, len, S, mn, mn);
        for (unsigned long i = 0; i < len + mn; i++) acc[off + i] ^= tmp[i];
    }
    memcpy(c, acc, (sa + sb) * 8);
    free(acc); free(tmp);
    return 0;
}
