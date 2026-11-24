# Deciding codes on single-tape machines

If `c` decides `L` within `t`, then on the input
word of every `x` the single-tape machine of `c` halts within `t |x| + 1` steps, with the answer
symbol `c.inputSym (L x)` under the head and every cell right of the head blank. The cells left of
the head read as the cells left of the head of `c` after `t |x|` steps.
