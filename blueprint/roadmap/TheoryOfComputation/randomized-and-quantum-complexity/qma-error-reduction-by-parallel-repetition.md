# QMA error reduction by parallel repetition

Let a verifier in the circuit model of the QMA definition have completeness $c(n)$ and soundness $s(n)$, where $c$ and $s$
are computable in time polynomial in $n$ and $c(n) - s(n) \ge 1/q(n)$ for a polynomial $q$, and let $p$ be a polynomial.
Running $k = \lceil 2 \ln 2 \cdot q(n)^2 (p(n) + 1) \rceil = O(q(n)^2 p(n))$ copies of the verifier on the $k$ registers of a
$k$-fold witness, of $k$ times the original witness length, and accepting when more than $\frac{c+s}{2}k$ copies accept gives
completeness at least $1 - 2^{-p(n)}$ and soundness at most $2^{-p(n)}$. Soundness holds for every witness, including
witnesses entangled across the $k$ registers: the acceptance operators of the copies commute, so the number of
accepting copies is analysed through the tensor power of the single-copy acceptance operator, whose eigenvalues are at
most $s(n)$, not by assuming independent witness blocks.

## Depends on

- [QMA for promise problems](local-hamiltonian-problem/qmapromise.md)
- [Polynomial-time computable functions](../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Sources

- C. Marriott and J. Watrous, "Quantum Arthur–Merlin games", arXiv:cs/0506068, Definition 3.1 and the paragraph after it ($a(n)$, $b(n)$ computable in polynomial time) and Theorem 3.2 (Kitaev), with its proof idea (threshold $(a+b)/2$, entangled certificates); Theorem 3.2 is proved in Kitaev, Shen and Vyalyi, *Classical and Quantum Computation*, Section 14.2, as cited there. <https://arxiv.org/abs/cs/0506068>
- J. Watrous, "Quantum computational complexity", arXiv:0804.3401, Section V.3 (weak error reduction by repetition on several copies of the quantum proof). <https://arxiv.org/abs/0804.3401>
- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §14.1 (error reduction by majority of repeated runs, safe against entangled witnesses). <https://arxiv.org/pdf/1907.09415v6>
