#ifndef GF2X_NEON_PCLMUL_SHIM_H_
#define GF2X_NEON_PCLMUL_SHIM_H_
/* Exact NEON/PMULL emulation of the SSE2/PCLMUL intrinsics used by the
 * x86_64_pclmul kernels (subset: immediates 0,1,0x10,0x11; byte shifts by 8;
 * 64-bit half swap). */
#include <arm_neon.h>
#include <stdint.h>
typedef uint64x2_t __m128i;
static inline __m128i gf2x_neon_clmul(__m128i a, __m128i b, int imm) {
    poly64_t x = (poly64_t) vgetq_lane_u64(a, 0);
    poly64_t y = (poly64_t) vgetq_lane_u64(b, 0);
    if (imm & 1)    x = (poly64_t) vgetq_lane_u64(a, 1);
    if (imm & 0x10) y = (poly64_t) vgetq_lane_u64(b, 1);
    return vreinterpretq_u64_p128(vmull_p64(x, y));
}
#define _mm_clmulepi64_si128(a,b,imm) gf2x_neon_clmul((a),(b),(imm))
#define _mm_loadu_si128(p) vld1q_u64((const uint64_t*)(p))
#define _mm_storeu_si128(p,v) vst1q_u64((uint64_t*)(p),(v))
#define _mm_setzero_si128() vdupq_n_u64(0)
#define _mm_xor_si128(a,b) veorq_u64((a),(b))
#define _mm_slli_si128(v,n) vreinterpretq_u64_u8(vextq_u8(vdupq_n_u8(0), vreinterpretq_u8_u64(v), 16-(n)))
#define _mm_srli_si128(v,n) vreinterpretq_u64_u8(vextq_u8(vreinterpretq_u8_u64(v), vdupq_n_u8(0), (n)))
#define _MM_SHUFFLE(a,b,c,d) (((a)<<6)|((b)<<4)|((c)<<2)|(d))
#define _mm_shuffle_epi32(x,imm) vextq_u64((x),(x),1) /* only (1,0,3,2) used */
#define _mm_unpacklo_epi64(a,b) vzip1q_u64((a),(b))
#define _mm_unpackhi_epi64(a,b) vzip2q_u64((a),(b))
#undef _gf2x_mm_setr_epi64
#undef _gf2x_mm_set1_epi64
#define _gf2x_mm_setr_epi64(lo,hi) vcombine_u64(vcreate_u64((uint64_t)(lo)), vcreate_u64((uint64_t)(hi)))
#define _gf2x_mm_set1_epi64(u) vdupq_n_u64((uint64_t)(u))
#endif
/* This file is part of the gf2x library.

   Copyright 2010, 2013, 2015
   Richard Brent, Pierrick Gaudry, Emmanuel Thome', Paul Zimmermann

   This program is free software; you can redistribute it and/or modify it
   under the terms of either:
    - If the archive contains a file named toom-gpl.c (not a trivial
    placeholder), the GNU General Public License as published by the Free
    Software Foundation; either version 3 of the License, or (at your
    option) any later version.
    - If the archive contains a file named toom-gpl.c which is a trivial
    placeholder, the GNU Lesser General Public License as published by
    the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.
   
   This program is distributed in the hope that it will be useful, but WITHOUT
   ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
   FITNESS FOR A PARTICULAR PURPOSE.  See the license text for more details.
   
   You should have received a copy of the GNU General Public License as
   well as the GNU Lesser General Public License along with this program;
   see the files COPYING and COPYING.LIB.  If not, write to the Free
   Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
   02110-1301, USA.
*/



#ifndef GF2X_MUL1_H_
#define GF2X_MUL1_H_

#include "gf2x.h"
/* All gf2x source files for lowlevel functions must include gf2x-small.h
 * This is mandatory for the tuning mechanism. */
#include "gf2x/gf2x-small.h"

#if GF2X_WORDSIZE != 64
#error "This code is for 64-bit only"
#endif


GF2X_STORAGE_CLASS_mul1 void
gf2x_mul1 (unsigned long *c, unsigned long a, unsigned long b)
{
    __m128i aa = _gf2x_mm_setr_epi64(a, 0);
    __m128i bb = _gf2x_mm_setr_epi64(b, 0);
    _mm_storeu_si128((__m128i*)c, _mm_clmulepi64_si128(aa, bb, 0));
}

GF2X_STORAGE_CLASS_mul_1_n unsigned long
gf2x_mul_1_n (unsigned long *cp, const unsigned long *bp, long sb, unsigned long a)
{
    long i;
    typedef union {
        __m128i s;
        unsigned long x[2];
    } __m128i_proxy;

    __m128i y = _gf2x_mm_set1_epi64(a);
    __m128i x;
    __m128i_proxy cc;


    // do two at a time
    for (i = 0; i + 2 < sb; i += 2) {
        x = _gf2x_mm_setr_epi64(bp[i], bp[i+1]);
        cc.s = _mm_clmulepi64_si128(x, y, 0);
        if (i == 0)
            cp[i] = cc.x[0];
        else
            cp[i] ^= cc.x[0];
        cp[i+1] = cc.x[1];
        cc.s = _mm_clmulepi64_si128(x, y, 1);
        cp[i+1] ^= cc.x[0];
        cp[i+2] = cc.x[1];
    }
    // last is different, to handle carry out
    unsigned long cy;
    if (i == sb - 2) {  // case bp is even
        x = _gf2x_mm_setr_epi64(bp[i], bp[i+1]);
        cc.s = _mm_clmulepi64_si128(x, y, 0);
        if (i == 0)
            cp[i] = cc.x[0];
        else
            cp[i] ^= cc.x[0];
        cp[i+1] = cc.x[1];
        cc.s = _mm_clmulepi64_si128(x, y, 1);
        cp[i+1] ^= cc.x[0];
        cy = cc.x[1];
    } else { //case bp is odd
        x = _gf2x_mm_setr_epi64(bp[i], 0);
        cc.s = _mm_clmulepi64_si128(x, y, 0);
        if (i == 0)
            cp[i] = cc.x[0];
        else
            cp[i] ^= cc.x[0];
        cy = cc.x[1];
    }
    return cy;
}

GF2X_STORAGE_CLASS_addmul_1_n unsigned long
gf2x_addmul_1_n (unsigned long *dp, const unsigned long *cp, const unsigned long* bp, long sb, unsigned long a)
{
    long i;
    typedef union {
        __m128i s;
        unsigned long x[2];
    } __m128i_proxy;

    __m128i y = _gf2x_mm_set1_epi64(a);
    __m128i x;
    __m128i_proxy dd;

    // do two at a time
    for (i = 0; i + 2 < sb; i += 2) {
        x = _gf2x_mm_setr_epi64(bp[i], bp[i+1]);
        dd.s = _mm_clmulepi64_si128(x, y, 0);
        if (i == 0)
            dp[i] = cp[i] ^ dd.x[0];
        else
            dp[i] ^= dd.x[0];
        dp[i+1] = cp[i+1] ^ dd.x[1];
        dd.s = _mm_clmulepi64_si128(x, y, 1);
        dp[i+1] ^= dd.x[0];
        dp[i+2] = cp[i+2] ^ dd.x[1];
    }
    unsigned long cy;
    if (i == sb - 2) {  // case bp is even
        x = _gf2x_mm_setr_epi64(bp[i], bp[i+1]);
        dd.s = _mm_clmulepi64_si128(x, y, 0);
        if (i == 0)
            dp[i] = cp[i] ^ dd.x[0];
        else
            dp[i] ^= dd.x[0];
        dp[i+1] = cp[i+1] ^ dd.x[1];
        dd.s = _mm_clmulepi64_si128(x, y, 1);
        dp[i+1] ^= dd.x[0];
        cy = dd.x[1];
    } else {
        x = _gf2x_mm_setr_epi64(bp[i], 0);
        dd.s = _mm_clmulepi64_si128(x, y, 0);
        if (i == 0)
            dp[i] = cp[i] ^ dd.x[0];
        else
            dp[i] ^= dd.x[0];
        cy = dd.x[1];
    }
    return cy;
}

#endif   /* GF2X_MUL1_H_ */
