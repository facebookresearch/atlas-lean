# Hardness magnification for Gap-MKtP near state-of-the-art lower bounds

Oliveira, Pich and Santhanam show that marginal lower bounds for the gap version of MKtP magnify to separations of EXP: barely superlinear bounds for circuits and parity-leaf formulas, and slightly super-quadratic or super-cubic bounds for formulas and branching programs, would give $\mathsf{EXP} \not\subseteq$ the corresponding polynomial-size class.

Let $N = 2^n$ be the input length and let $\mathrm{Gap\text{-}MKtP}[s_1, s_2]$ be the promise problem with yes-instances $\{x \in \{0,1\}^N : Kt(x) \le s_1(N)\}$ and no-instances $\{x \in \{0,1\}^N : Kt(x) > s_2(N)\}$. There is a universal constant $c \ge 1$ such that the following hold. If there is $\varepsilon > 0$ such that for every small enough $\beta > 0$:

1. $\mathrm{Gap\text{-}MKtP}[2^{\beta n}, 2^{\beta n} + c n] \notin \mathsf{Circuit}[N^{1+\varepsilon}]$, then $\mathsf{EXP} \not\subseteq \mathsf{Circuit}[\mathrm{poly}]$;
2. $\mathrm{Gap\text{-}MKtP}[2^{\beta n}, 2^{\beta n} + c n] \notin U_2\text{-}\mathsf{Formula}\text{-}\oplus[N^{1+\varepsilon}]$, then $\mathsf{EXP} \not\subseteq \mathsf{Formula}[\mathrm{poly}]$;
3. $\mathrm{Gap\text{-}MKtP}[2^{\beta n}, 2^{\beta n} + c n] \notin B_2\text{-}\mathsf{Formula}[N^{2+\varepsilon}]$, then $\mathsf{EXP} \not\subseteq \mathsf{Formula}[\mathrm{poly}]$;
4. $\mathrm{Gap\text{-}MKtP}[2^{\beta n}, 2^{\beta n} + c n] \notin U_2\text{-}\mathsf{Formula}[N^{3+\varepsilon}]$, then $\mathsf{EXP} \not\subseteq \mathsf{Formula}[\mathrm{poly}]$;
5. $\mathrm{Gap\text{-}MKtP}[2^{\beta n}, 2^{\beta n} + c n] \notin \mathsf{BP}[N^{2+\varepsilon}]$, then $\mathsf{EXP} \not\subseteq \mathsf{BP}[\mathrm{poly}]$;
6. $\mathrm{Gap\text{-}MKtP}[2^{\beta n}, 2^{\beta n} + c n] \notin \mathsf{AC}^0[6][N^{1+\varepsilon}]$, then $\mathsf{EXP} \not\subseteq \mathsf{AC}^0[6]$.

Here $U_2$-formulas use fan-in-two AND and OR, $B_2$-formulas use all binary gates, formula size counts leaves, $\mathsf{BP}[s]$ is deterministic branching programs of size $s$, and circuit size counts gates. The source also gives the analogous statements for $\mathsf{AND}\text{-}\mathsf{THR}\text{-}\mathsf{THR}\text{-}\mathsf{XOR}$ circuits and bounded-depth majority circuits.

## Proof sketch

The proof is by contraposition. An error-correcting code is applied to the input; since Kt grows by at most the logarithm of the running time under polynomial-time maps, the codeword of a low-complexity string still has low Kt, while the decoder shows that the codeword of a high-complexity string is far from every low-complexity string. A derandomized random projection then shrinks the instance to length $\mathrm{poly}(2^{\beta n}) \ll N$, an instance of a problem in EXP that the assumed collapse solves cheaply. The thresholds differ between models only through the cost of computing the code: parities at the leaves cost nothing for item 2, while plain formulas pay a quadratic or cubic factor.

## Depends on

- [The minimum Kt problem MKtP](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/the-minimum-kt-problem.md)
- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)
- [Formula-XOR circuits and their local oracle extension](formula-xor-circuits.md)
- [The class EXP](../../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [Polynomial time with polynomial advice](../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [The class AC^0(m)](../../../complexity-classes/time-and-space-complexity-classes/ac0-mod.md)

## Proof depends on

None.

## Sources

- Igor C. Oliveira, Ján Pich and Rahul Santhanam, "Hardness Magnification Near State-of-the-Art Lower Bounds", *Theory of Computing* 17(11), 2021 (CCC 2019 special issue), DOI 10.4086/toc.2021.v017a011 (Theorem 1.1, items 1, 2, 5, 6, 7 and 8; Definitions 2.1 and 2.2; proof in Sections 3.1 and 3.2).
