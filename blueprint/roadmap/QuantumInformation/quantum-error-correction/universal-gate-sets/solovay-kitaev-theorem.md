# The Solovay–Kitaev theorem

Let $\mathcal{G}$ be an [instruction set](instruction-set.md) for $SU(d)$. There is a constant $c$ such that for every
$U \in SU(d)$ and every $\varepsilon > 0$ there is a finite sequence $g_1, \dots, g_m$ of
elements of $\mathcal{G}$ with

$$m = O\big(\log^{c} (1/\varepsilon)\big) \qquad\text{and}\qquad \| U - g_1 \cdots g_m \| < \varepsilon ,$$

the implied constant depending on $\mathcal{G}$ only (the bound concerns $\varepsilon \to 0$). The Dawson–Nielsen proof gives $c = \ln 5 / \ln (3/2) \approx 3.97$.
Their algorithm finds the sequence classically in time $O(\log^{\ln 3/\ln(3/2)} (1/\varepsilon)) \approx O(\log^{2.71}(1/\varepsilon))$
when the output is a compressed representation with pointers to repeated subsequences, and in time
$O(\log^{3.97}(1/\varepsilon))$ when the gate list is written out; both count arithmetic operations on exactly specified
matrices, not the cost of finite-precision arithmetic. For a circuit of $N$ gates, each acting on at most a fixed number
$m$ of qubits, write each gate as a phase times a gate of determinant one, $G_i = e^{i\theta_i} G_i'$ with $G_i' \in SU(2^m)$,
and approximate each $G_i'$ within $\varepsilon/N$ by an instruction set for $SU(2^m)$. This gives a circuit of
$O(N \log^{c}(N/\varepsilon))$ instructions within $\varepsilon$ of the original up to the global phase
$e^{i(\theta_1 + \cdots + \theta_N)}$, the constant depending on $m$ and the instruction set. The phases cannot be dropped:
for $U = iI$ on one qubit, every product of elements of $SU(2)$ has eigenvalues $e^{\pm it}$ and so is at distance at
least $\sqrt 2$ from $U$. No bound of this form holds uniformly in the gate width, since a single gate on $n$ qubits can be an
arbitrary $n$-qubit unitary.

## Expansion

A good expansion adds pages for the remaining steps of the Dawson–Nielsen proof: the balanced group commutator
decomposition, which takes two forms: in $SU(2)$ it is exact (Section 4.1, equation (11)): every $U$ with
$\|I - U\| < \varepsilon$ equals $V W V^{*} W^{*}$ with $\|I - V\|, \|I - W\| \le c_{gc}\sqrt{\varepsilon}$; in $SU(d)$ for fixed
$d$ the construction (Sections 5.1–5.2) only approximates, giving $V, W$ within $O_d(\sqrt{\varepsilon})$ of $I$ with
$V W V^{*} W^{*}$ within $O_d(\varepsilon^{3/2})$ of $U$; the existence of an
$\varepsilon_0$-net of $SU(d)$ by products of bounded length (the base case, from density); and the recursion analysis
giving the exponents. The [commutator approximation lemma](approximating-a-group-commutator.md) is already a page.

## Depends on

- [Instruction set for $SU(d)$](instruction-set.md)

## Proof depends on

- [Approximating a group commutator](approximating-a-group-commutator.md)
- [Telescoping bound for products of contractions](../../not-yet-classified/part-01/unitary-error-budget/norm-list-of-fn-prod-sub-le.md)

## Background

- [Clifford plus $T$ is universal](clifford-plus-t-is-universal.md)

## Sources

- C. M. Dawson and M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006), 81–95, arXiv:quant-ph/0505030, Section 2, Theorem 1 and the discussion after it (running time with and without compressed output, compilation of an $m$-gate circuit), Section 3 (the algorithm, its recurrences and equation (9)), Section 4 and Section 5.
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.5 (polylog$(1/\epsilon)$ gates suffice).
