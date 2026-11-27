# Agrawal–Vinay–Koiran–Tavenas reduction to depth four

Let $f \in \mathbb{F}[x_1, \dots, x_n]$ be homogeneous of degree $d$ and computed by an arithmetic circuit of size $s$ with $s \ge n$. Then $f$ is computed by a homogeneous $\Sigma\Pi^{[O(\sqrt{d})]}\Sigma\Pi^{[\sqrt{d}]}$ circuit of size $s^{O(\sqrt{d})}$. Over every field, the same conclusion holds for formulas of size $s$ and for algebraic branching programs. More generally, for every cut parameter $b \in [1, d]$, $f$ is computed by a homogeneous $\Sigma^{[T]}\Pi^{[O(d/b)]}\Sigma\Pi^{[b]}$ circuit with top fan-in $T = s^{O(d/b)}$ and each bottom $\Sigma\Pi^{[b]}$ subcircuit a sum of at most $n^{O(b)}$ monomials (Tavenas, arXiv:1304.5777, Lemma 3 and the proof of Theorem 1; taking $b = \sqrt{d}$ recovers the bound above).

## Proof sketch

Apply depth reduction to obtain a circuit of depth $O(\log d)$ in which each multiplication gate has children of degree at most a constant fraction of its own. Expand the resulting expression top-down, cutting at gates of degree about $\sqrt{d}$: every monomial of the expansion becomes a product of $O(\sqrt{d})$ polynomials of degree at most $\sqrt{d}$, each a sum of at most $s^{O(\sqrt{d})}$ monomials, and the number of expansion terms is $s^{O(\sqrt{d})}$. Tavenas's careful choice of cut levels (Lemma 3 on a homogeneous $\times$-balanced circuit of size $\sigma = \mathrm{poly}(s)$, giving a homogeneous $\Sigma\Pi^{[15a]}\Sigma\Pi^{[d/a]}$ circuit of size $1 + \binom{\sigma+15a}{15a} + \sigma + \sigma\binom{n+d/a}{d/a} + n$ for any $0 < a < d$, setting $a = d/b$) yields both the general-$b$ tradeoff and the optimal $b = \sqrt{d}$ bottom fan-in.

## Depends on

- [Homogeneous depth-four circuits with bounded bottom fan-in](homogeneous-depth-four.md)
- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Proof depends on

- [Valiant–Skyum–Berkowitz–Rackoff depth reduction](vsbr-depth-reduction.md)

## Sources

- M. Agrawal, V. Vinay, "Arithmetic circuits: a chasm at depth four", FOCS (2008).
- P. Koiran, "Arithmetic circuits: the chasm at depth four gets wider", Theoretical Computer Science 448 (2012) 56-65.
- S. Tavenas, "Improved bounds for reduction to depth 4 and depth 3", Information and Computation 240 (2015) 2-11; MFCS (2013); arXiv:1304.5777 (Lemma 3 and Theorem 1).
