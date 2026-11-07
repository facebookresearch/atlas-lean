# Declared polynomial time for timed functions on bitstrings

Let $f$ be a timed function
that maps each list $x$ of Booleans to an output list $f(x)$ of Booleans together with a declared
time $t_f(x) \in \mathbb{N}$. Then $f$ computes in declared polynomial time when there is a
polynomial $p$ with natural-number coefficients such that, for every list $x$ of Booleans, both
$t_f(x)$ and the length of $f(x)$ are at most $p(|x|)$, where $|x|$ is the length of $x$.

Declared times are trusted annotations, not checked against any machine model, so this does not
make $f$ polynomial-time computable: for an arbitrary decision problem $L$, the function returning
the one-element list $[L(x)]$ with declared time $0$ satisfies it. The output-length bound is what
lets declared bounds compose.
