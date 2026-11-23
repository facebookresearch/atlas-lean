# A timed verifier with polynomial-time output function puts its language in NP

Let $L$ be
a decision problem, $p$ a polynomial with natural-number coefficients, and $V$ a timed function
from pairs of lists of Booleans to Booleans that verifies $L$ with witness bound $p$. If the
function sending $(x, w)$ to the output of $V$ on $(x, w)$ is polynomial-time computable by a
Turing machine for the canonical bitstring encodings, then $L$ is in NP.

The polynomial-time hypothesis must be proved separately for $V$; it does not follow from any
bound on the declared time of $V$.
