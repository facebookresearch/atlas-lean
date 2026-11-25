# Declared polynomial time is preserved under precomposition with a reduction

Let $L_1$ and
$L_2$ be decision problems, let $f$ be a declared-time many-one reduction from $L_1$ to $L_2$, and
let $g$ be a timed function from lists of Booleans to Booleans that decides in declared polynomial
time. Then the timed function that on input $x$ returns $g(f(x))$, with declared time the declared
time of $f$ on $x$ plus that of $g$ on $f(x)$, decides in declared polynomial time.

If $p_f$ bounds the declared time and output length of $f$ and $p_g$ bounds the declared time of
$g$, then $p_f + p_g \circ p_f$ bounds the declared time of the composite.
