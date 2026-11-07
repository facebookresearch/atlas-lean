# From declared-time to polynomial-time many-one reductions

Let $L_1$ and $L_2$ be decision
problems and let $f$ be a declared-time many-one reduction from $L_1$ to $L_2$. If the function
sending $x$ to the output of $f$ on $x$ is polynomial-time computable by a Turing machine for the
canonical bitstring encodings, then $L_1$ reduces to $L_2$ by a polynomial-time many-one
reduction.

The polynomial-time hypothesis must be proved separately for $f$; it does not follow from the
declared-time bound.
