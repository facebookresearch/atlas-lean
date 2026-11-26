# The frontier lower bound for circuits of bounded fan-in

Fix a fan-in bound $r\ge2$ and assume the layout hypothesis $\mathrm{LB}(r+1,A)$. Let $S_n\subseteq U^n$ be $K_n$-rectangle-free sets over a finite alphabet $U$ with $\log K_n=o(n)$ and $|S_n|\ge|U|^{n-o(n)}$. Then for every $\varepsilon>0$ and all large $n$, every circuit over any basis of fan-in at most $r$ on $U$ that decides $S_n$ has $s$ multiary gates with

$$
(r-1)s>\Bigl(1+\frac1A-\varepsilon\Bigr)n .
$$

For fan-in two the bound reads $s>(1+1/A-\varepsilon)n$.

## Proof sketch

Compile the circuit to a network; a layout of width $(A+o(1))\beta_1+o(n)$ gives a sweep with at most $|U|^{\text{width}}$ messages, and the counting lemma yields $|S_n|\le K_n^2\cdot T\cdot|U|^{2\,\text{width}+O(1)}$. Since $|S_n|\ge|U|^{n-o(n)}$, the width must be nearly $n/2$ at some step; with $\beta_1\le(r-1)s+1-n$ (inputs read are subtracted) this forces the stated bound.

## Depends on

- [Rectangle-free sets and rectangle bias](rectangle-free-sets-and-rectangle-bias.md)
- [Layouts of multigraphs, cycle rank and the layout hypothesis](layouts-and-the-layout-hypothesis.md)

## Proof depends on

- [From small circuits to wide constraint networks](from-circuits-to-constraint-networks.md)
- [Sweeps and the frontier counting lemma](sweeps-and-the-frontier-counting-lemma.md)

## Sources

- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
