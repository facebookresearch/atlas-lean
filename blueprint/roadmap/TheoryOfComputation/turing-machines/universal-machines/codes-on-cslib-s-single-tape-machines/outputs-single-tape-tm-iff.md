# Exactly when CSLib's output convention holds

If `c` decides `L` within `t`, the
single-tape machine of `c` outputs `[c.inputSym (L x)]` on the input word of `x`, after some
finite number of steps, if and only if every cell left of the head of `c` is blank after `t |x|`
steps on `x`.
