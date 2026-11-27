# Constructive separations of MCSP from AC0 imply P ≠ NP

Although MCSP is known not to be in $\mathsf{AC}^0$, a polylogtime-uniform $\mathsf{AC}^0$ refuter of quasi-polynomial size for MCSP against every uniform $\mathsf{AC}^0$ algorithm would separate P from NP; such refuters exist under a standard hypothesis, and slightly weaker ones exist unconditionally.

Let $s(n) \ge n^{\log(n)^{\omega(1)}}$ be time-constructive and super-quasipolynomial, and consider $\mathrm{MCSP}[s(n)]$ and Parity on inputs of length $N = 2^n$. A polylogtime-uniform $\mathsf{AC}^0[f(n)]$-refuter for $\mathrm{MCSP}[s(n)]$ against $A$ is a polylogtime-uniform $\mathsf{AC}^0$ circuit of size $f(n)$ that on input $1^N$ outputs $x \in \{0,1\}^N$ such that, for infinitely many $N = 2^n$, the output $A(x)$ differs from the membership of $x$ in $\mathrm{MCSP}[s(n)]$. Then:

1. if for every polylogtime-uniform $\mathsf{AC}^0$ algorithm there is a polylogtime-uniform $\mathsf{AC}^0[\mathrm{quasipoly}]$ refuter for $\mathrm{MCSP}[s(n)]$, then $\mathsf{P} \ne \mathsf{NP}$;
2. if $\mathsf{PH} \not\subseteq \mathsf{SIZE}(s(n)^2)$, such refuters exist against every polylogtime-uniform $\mathsf{AC}^0$ algorithm;
3. for $s(n) \le o(2^n/n)$ there is, against every polylogtime-uniform $\mathsf{AC}^0$ algorithm, a polylogtime-uniform $\mathsf{AC}^0[2^{\mathrm{poly}(s(n))}]$ refuter for $\mathrm{MCSP}[s(n)]$;
4. there is a polylogtime-uniform $\mathsf{AC}^0[\mathrm{quasipoly}]$ list-refuter for Parity against every polylogtime-uniform $\mathsf{AC}^0$ algorithm.

## Proof sketch

Item 1 already holds for refuters against the constant-one algorithm: if $\mathsf{P} = \mathsf{NP}$, every string printed by a polylogtime-uniform quasi-polynomial-size $\mathsf{AC}^0$ refuter has circuit complexity $2^{(\log\log N)^{O(1)}}$, hence is a yes-instance of $\mathrm{MCSP}[s(n)]$ and cannot refute the algorithm that always accepts. Item 2 is a win-win: Nisan's generator $G$ fooling depth-$d$ $\mathsf{AC}^0$ has outputs of circuit complexity $\mathrm{polylog}(N)$, and its translate $G \oplus y_N$ by the truth table $y_N$ of a $\mathsf{PH}$ function outside $\mathsf{SIZE}(s(n)^2)$ has outputs of high circuit complexity; if the algorithm rejects a random input with probability at least $1/2$ the refuter finds a rejected output of $G$, and otherwise an accepted output of the translate. Item 3 replaces the translate by the sparsity of yes-instances, at the price of size $2^{\mathrm{poly}(s(n))}$, only slightly super-quasipolynomial in $N$. Together the items form a frontier for constructive lower bounds analogous to hardness magnification frontiers.

## Depends on

- [Refuters and constructive separations](constructive-separation.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [The class AC^0](../../../complexity-classes/time-and-space-complexity-classes/ac0.md)
- [The polynomial hierarchy](../../../complexity-classes/time-and-space-complexity-classes/ph.md)
- [The P versus NP question](../../../complexity-classes/the-classes-p-np-and-conp/the-p-versus-np-problem.md)
- [The class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The parity language](../../../complexity-classes/time-and-space-complexity-classes/parity-dec.md)

## Proof depends on

None.

## Sources

- Lijie Chen, Ce Jin, Rahul Santhanam and Ryan Williams, "Constructive Separations and Their Consequences", *TheoretiCS* 3, 2024 (conference version FOCS 2021), DOI 10.46298/theoretics.24.3, arXiv:2203.14379v5 (Theorem 1.7, Section 1.2; items 1 to 4 proved as Propositions 4.3, 4.4, 4.5 and 4.7, Section 4).
