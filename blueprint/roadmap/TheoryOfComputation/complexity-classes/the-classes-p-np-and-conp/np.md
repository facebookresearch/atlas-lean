# The complexity class NP

NP is the set of decision problems $L$ (functions from lists of
booleans to booleans) for which there exist a polynomial $p$ with natural-number coefficients and
a polynomial-time computable function $R$ from pairs of lists of booleans to booleans such that,
for every list of booleans $x$, $L(x)$ is true if and only if there is a list of booleans $w$
whose length is at most $p$ evaluated at the length of $x$ and for which $R(x, w)$ is true.

Polynomial time is measured with respect to the canonical bitstring encodings.

## Sources

- adapted from FormalConjectures, FormalConjecturesForMathlib/Computability/Complexity.lean (absent from Mathlib).
