# Add Correction

The integral polynomial `(x ^ p + y ^ p - (x + y) ^ p) / p`, written as
`-∑_{0 < i < p} x ^ i y ^ (p - i) (p.choose i / p)`. For prime `p` it satisfies
`p * addCorrection p x y = x ^ p + y ^ p - (x + y) ^ p` (`natCast_mul_addCorrection`).
