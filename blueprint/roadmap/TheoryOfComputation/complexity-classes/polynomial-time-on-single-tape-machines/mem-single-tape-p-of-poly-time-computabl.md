# CSLib's polynomial-time functions decide `SingleTapeP` problems

Assume that `Symbol` is inhabited (it has a designated default element).

If a CSLib
`SingleTapeTM.PolyTimeComputable` function `f` over a finite alphabet maps every encoded input
`w.map ι` to the one-symbol answer `[ι (L w)]`, for an injective `ι`, then `L ∈ SingleTapeP`, with
the same machine and polynomial.
