# One-way function families

Let $f$ assign to each $n \in \mathbb{N}$ and each $n$-bit
string $x$ a bitstring $f_n(x)$. The family $f$ is one-way when three conditions hold. First, its
output lengths are polynomially bounded: some polynomial $p$ satisfies $|f_n(x)| \le p(n)$ for
all $n$ and $x$. Second, it is uniformly computable: some polynomial-time computable function
maps the bitstring encoding of the pair $(n, x)$ to $f_n(x)$ for all $n$ and $x$. Third, it is
hard to invert: for every polynomial $q$ with natural-number coefficients and every
polynomial-time computable inverter $A$ on triples $(n, y, r)$ of a natural number and two
bitstrings, the inversion success probability of $A$ against $f$ at length $n$ with $q(n)$
coins is negligible in $n$, that is, for every $c \in \mathbb{N}$ it is at most $1 / n^c$ for
all large enough $n$. Here the inversion success probability is the fraction of pairs $(x, r)$
of an $n$-bit string $x$ and a $q(n)$-bit string $r$ for which the $n$-bit string $x'$ formed
by the first $n$ bits of $A(n, f_n(x), r)$, with missing bits false, satisfies
$f_n(x') = f_n(x)$.

Deterministic inverters are the special case that ignores the coins. The uniform evaluator is
essential: per-length polynomial-size circuits would admit arbitrary noncomputable families.

## Sources

- O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University Press, 2001, Section 2.2; R. Impagliazzo, "A personal view of average-case complexity", Proceedings of the Tenth Annual Structure in Complexities Theory Conference (1995), 134-147.
