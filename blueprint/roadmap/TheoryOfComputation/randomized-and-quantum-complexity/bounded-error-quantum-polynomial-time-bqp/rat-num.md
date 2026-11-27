# Signed numerator of an encoded rational

The numerator field with the stored sign, or `0`
when the stored denominator is `0` (the encoded value is then `0` while the numerator field may be
nonzero). Together with `ratDenom`, `toRat e = ratNum e / ratDenom e`.
