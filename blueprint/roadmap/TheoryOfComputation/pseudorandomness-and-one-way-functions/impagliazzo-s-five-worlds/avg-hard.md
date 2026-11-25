# Hard on average

Let $p$ be a polynomial with natural-number coefficients, $L$ a
decision problem, and $S$ a family of samplers, where $S_n$ sends each string $r$ of $p(n)$
random bits to a bitstring $S_n(r)$. The pair $(L, S)$ is hard on average when it is not easy
on average: there is no polynomial-time computable function $A$ from bitstrings to booleans
such that for every natural number $c$ and all sufficiently large $n$, $A$ agrees with $L$ on
$S_n(r)$ for at least a fraction $1 - 1/(n^c + 1)$ of the $2^{p(n)}$ coin strings $r$.

Since hardness is the logical complement of easiness, if $\mathrm{P} \ne \mathrm{NP}$ and
Heuristica fails, then some NP problem is hard on average for some samplable ensemble.
