# Majority decoding corrects a single bit flip

Majority decoding undoes any single bit flip of a codeword label: for every
logical bit `b : Fin 2` and every position `j : Fin 3`, `recoverBasis
(flipAt j (encodeQ b)) = encodeQ b`. Here `encodeQ` sends `0` to the label
`000` and `1` to `111`.
