# Agrawal–Vinay–Koiran–Tavenas reduction to depth four

Let $f \in \mathbb{F}[x_1, \dots, x_n]$ be homogeneous of degree $d$ and computed by an arithmetic circuit of size $s$ with $s \ge n$. Then $f$ is computed by a homogeneous $\Sigma\Pi^{[O(\sqrt{d})]}\Sigma\Pi^{[\sqrt{d}]}$ circuit of size $s^{O(\sqrt{d})}$. Over every field, the same conclusion holds for formulas of size $s$ and for algebraic branching programs.

## Proof sketch

Apply depth reduction to obtain a circuit of depth $O(\log d)$ in which each multiplication gate has children of degree at most a constant fraction of its own. Expand the resulting expression top-down, cutting at gates of degree about $\sqrt{d}$: every monomial of the expansion becomes a product of $O(\sqrt{d})$ polynomials of degree at most $\sqrt{d}$, each a sum of at most $s^{O(\sqrt{d})}$ monomials, and the number of expansion terms is $s^{O(\sqrt{d})}$. Tavenas's careful choice of cut levels gives the optimal $\sqrt{d}$ bottom fan-in.

## Depends on

- [Homogeneous depth-four circuits with bounded bottom fan-in](homogeneous-depth-four.md)
- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Proof depends on

- [Valiant–Skyum–Berkowitz–Rackoff depth reduction](vsbr-depth-reduction.md)

## Sources

- M. Agrawal, V. Vinay, "Arithmetic circuits: a chasm at depth four", FOCS (2008).
- P. Koiran, "Arithmetic circuits: the chasm at depth four gets wider", Theoretical Computer Science 448 (2012) 56-65.
- S. Tavenas, "Improved bounds for reduction to depth 4 and depth 3", Information and Computation 240 (2015) 2-11; MFCS (2013).
