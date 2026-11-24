# CSLib's output convention

If `c` decides `L` within `t` and every cell left of the head
of `c` is blank after `t |x|` steps on `x`, then the single-tape machine of `c` outputs
`[c.inputSym (L x)]` on the input word of `x` within `t |x| + 1` steps.
