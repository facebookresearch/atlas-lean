# The Solovay–Kitaev theorem

Let $\mathcal{G}$ be an [instruction set](instruction-set.md) for $SU(d)$. There is a constant $c$ such that for every
$U \in SU(d)$ and every $\varepsilon > 0$ (with $\varepsilon < 1/2$, say) there is a finite sequence $g_1, \dots, g_m$ of
elements of $\mathcal{G}$ with

$$m = O\big(\log^{c} (1/\varepsilon)\big) \qquad\text{and}\qquad \| U - g_1 \cdots g_m \| < \varepsilon ,$$

the implied constant depending on $\mathcal{G}$ only. The Dawson–Nielsen proof gives $c = \ln 5 / \ln (3/2) \approx 3.97$,
and their algorithm finds the sequence classically in time $O(\log^{\ln 3/\ln(3/2)} (1/\varepsilon)) \approx O(\log^{2.71}(1/\varepsilon))$.
Combined with a universal gate set closed under inverses, a circuit of $N$ arbitrary gates is approximated to accuracy
$\varepsilon$ by $O(N \log^{c}(N/\varepsilon))$ gates from the set.

## Expansion

A good expansion adds pages for the remaining steps of the Dawson–Nielsen proof: the balanced group commutator
decomposition (every $U$ with $\|I - U\| < \varepsilon$ is $V W V^{*} W^{*}$ with $\|I - V\|, \|I - W\| \le c_{gc}\sqrt{\varepsilon}$,
proved there only approximately for $SU(2)$ in Section 4.1 and sketched for $SU(d)$ in Section 5); the existence of an
$\varepsilon_0$-net of $SU(d)$ by products of bounded length (the base case, from density); and the recursion analysis
giving the exponents. The [commutator approximation lemma](approximating-a-group-commutator.md) is already a page.

## Depends on

- [Instruction set for $SU(d)$](instruction-set.md)

## Proof depends on

- [Approximating a group commutator](approximating-a-group-commutator.md)

## Background

- [Clifford plus $T$ is universal](clifford-plus-t-is-universal.md)

## Sources

- C. M. Dawson and M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006), 81–95, arXiv:quant-ph/0505030, Section 2, Theorem 1, Section 3 (the algorithm and its recurrences) and Section 4.
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.5 (polylog$(1/\epsilon)$ gates suffice).
