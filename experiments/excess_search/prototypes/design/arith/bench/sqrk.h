// Custom squaring + sparse-modulus reduction kernel (aarch64 PMULL or x86 PCLMUL).
// P = x^E + sum_{k in ks} x^k + 1, all k < E/2 (so two folds suffice).
#pragma once
#include <cstdint>
#include <vector>
#include <cstring>
#if defined(__aarch64__)
#include <arm_neon.h>
static inline void spread2(const uint64_t* a, uint64_t* out) { // out[0..3] = spread(a[0]), spread(a[1])
    uint64x2_t v = vld1q_u64(a);
    poly128_t lo = vmull_p64((poly64_t)vgetq_lane_u64(v,0), (poly64_t)vgetq_lane_u64(v,0));
    poly128_t hi = vmull_high_p64(vreinterpretq_p64_u64(v), vreinterpretq_p64_u64(v));
    vst1q_u64(out, vreinterpretq_u64_p128(lo));
    vst1q_u64(out+2, vreinterpretq_u64_p128(hi));
}
#else
#include <immintrin.h>
static inline void spread2(const uint64_t* a, uint64_t* out) {
    __m128i v = _mm_loadu_si128((const __m128i*)a);
    _mm_storeu_si128((__m128i*)out, _mm_clmulepi64_si128(v, v, 0x00));
    _mm_storeu_si128((__m128i*)(out+2), _mm_clmulepi64_si128(v, v, 0x11));
}
#endif
static inline uint64_t ext64(const uint64_t* c, uint64_t pos) {
    uint64_t w = pos >> 6, s = pos & 63;
    return s ? (c[w] >> s) | (c[w+1] << (64 - s)) : c[w];
}
struct SparseSq {
    long E, nw; std::vector<long> ks; // ks excludes the constant term; reduction adds k=0 too
    std::vector<uint64_t> c; // scratch 2nw+2 words
    SparseSq(long E_, std::vector<long> ks_) : E(E_), nw((E_+63)/64), ks(ks_), c(2*((E_+63)/64)+4,0) {}
    // r <- reduce(c) where c has degree < 2E-1 (stored in c, length >= 2nw+2 zero padded)
    void reduce(uint64_t* r) {
        // fold 1: r = lo + sum_k x^k * hi, hi = c >> E (degree < E-1)
        long nhi = (E - 1 + 63) / 64; // words of hi
        // lo part
        for (long w = 0; w < nw; w++) r[w] = c[w];
        if (E & 63) r[nw-1] &= (~0ULL) >> (64 - (E & 63));
        // extra overflow words
        long kmax = 0; for (long k : ks) if (k > kmax) kmax = k;
        long nov = (kmax + 63)/64 + 1;
        uint64_t ov[64] = {0};
        // add hi << k for k in {0} U ks : word w of (hi<<k) = ext64(hi, 64w - k) where hi bit j = c bit E+j
        std::vector<long> all(ks); all.push_back(0);
        for (long k : all) {
            // positions 64w - k for w >= 0; for w with 64w < k handle partial
            long w0 = (k + 63) / 64; // first w with 64w >= k
            // partial word at w0-1 (if k%64): bits of hi shifted
            if (k & 63) { long w = w0 - 1; uint64_t v = c[(E)>>6]; (void)v;
                // bits of (hi<<k) in word w: hi bits [0, 64(w+1)-k) placed at offset k-64w
                uint64_t val = ext64(c.data(), E) << (k - 64*w); r[w] ^= val; }
            long top = nw; // r words
            for (long w = w0; w < top; w++) r[w] ^= ext64(c.data(), E + 64*w - k);
            // overflow beyond nw: words nw..nw+nov
            for (long w = top; w < top + nov; w++) { long pos = 64*w - k; if (pos < E) ov[w-top] ^= ext64(c.data(), E + pos); }
        }
        // bits of r at positions >= E (in last word) and ov constitute degree>=E part: fold again (small)
        // collect t = (r_hi_bits | ov) >> E as small poly, then r ^= sum x^k t
        uint64_t t[70] = {0}; long tw = nov + 1;
        // gather bits >= E from r[nw-1] and ov into t
        uint64_t tmp[72] = {0}; tmp[0] = r[nw-1]; for (long i = 0; i < nov; i++) tmp[1+i] = ov[i];
        long base = 64*(nw-1);
        for (long i = 0; i < tw; i++) t[i] = ext64(tmp, (E - base) + 64*i);
        // need t's bits beyond computed range zero: ext reads tmp up to index tw+1, fine (zeros)
        if (E & 63) r[nw-1] &= (~0ULL) >> (64 - (E & 63));
        for (long k : all) {
            for (long i = 0; i < tw; i++) {
                if (!t[i]) continue;
                long pos = 64*i + k; long w = pos >> 6, s = pos & 63;
                if (w < nw) r[w] ^= t[i] << s;
                if (s && w + 1 < nw) r[w+1] ^= t[i] >> (64 - s);
            }
        }
    }
    void sqr(uint64_t* r, const uint64_t* a) { // a has nw words, reduced
        long i = 0;
        for (; i + 1 < nw; i += 2) spread2(a + i, c.data() + 2*i);
        if (i < nw) { uint64_t tmp2[2] = {a[i], 0}; uint64_t o[4]; spread2(tmp2, o); c[2*i] = o[0]; c[2*i+1] = o[1]; }
        for (long j = 2*nw; j < (long)c.size(); j++) c[j] = 0;
        reduce(r);
    }
};
