# Superpolynomial extended Frege lower bounds imply that PV does not prove P = NP

Cook's theorem: if some polynomial-size tautologies require superpolynomial extended Frege proofs, then for no polynomial-time function symbol $g$ does $\mathsf{PV}$ prove that $g$ finds satisfying assignments of all satisfiable formulas. Thus EF lower bounds would make $\mathsf{P} \ne \mathsf{NP}$ consistent with $\mathsf{PV}$.

For an $\mathcal{L}_{\mathsf{PV}}$-function symbol $g$ let

$$
\mathsf{PNP}[g] = \forall 1^n\ \forall F\ \forall x\ \big((\mathsf{Formula}(F, 1^n) \wedge \mathsf{Sat}(F, x)) \rightarrow \mathsf{Sat}(F, g(F))\big),
$$

where $\mathsf{Formula}(F, 1^n)$ checks that $F$ describes a formula on $n$ input bits and $\mathsf{Sat}(F, x)$ checks that $x$ satisfies it. Suppose there is a sequence $\{F_n\}_{n \ge 1}$ of propositional tautologies of size polynomial in $n$ that require $\mathsf{EF}$-proofs of size $n^{\omega(1)}$. Then there is no function symbol $g$ such that $\mathsf{PV} \vdash \mathsf{PNP}[g]$.

## Proof sketch

Contrapositively, if $\mathsf{PV} \vdash \mathsf{PNP}[g]$, define the proof system $P_g$ accepting $\tilde\pi$ as a proof of $F$ iff $g(\neg F) = \tilde\pi$ and $\tilde\pi$ does not satisfy $\neg F$. Then $\mathsf{PV}$ proves the soundness of $P_g$, Cook's translation gives polynomial-size $\mathsf{EF}$-proofs of the translated soundness formulas, and instantiating them at an actual formula $F$ and its $P_g$-proof $g(\neg F)$, then using that $\mathsf{EF}$ proves $\|\mathsf{Sat}(\langle F\rangle, x)\| \rightarrow F(x)$ efficiently, gives a polynomial-size $\mathsf{EF}$-proof of every tautology. Since $\mathsf{PV}$ proves $\mathsf{P} = \mathsf{NP}$ iff it proves $\mathsf{NP} = \mathsf{coNP}$, such lower bounds also give the consistency of $\mathsf{NP} \ne \mathsf{coNP}$ with $\mathsf{PV}$.

## Depends on

- [Cook's theory PV of polynomial-time reasoning](../bounded-arithmetic-and-witnessing/cooks-theory-pv.md)
- [Cook–Reckhow propositional proof systems](../../../../Logic/propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)
- [The P versus NP problem](../../../complexity-classes/the-classes-p-np-and-conp/the-p-versus-np-problem.md)

## Proof depends on

None.

## Sources

- Igor C. Oliveira, "SIGACT News Complexity Theory Column 124: Meta-Mathematics of Computational Complexity Theory", *ACM SIGACT News* 56(1), 2025, DOI 10.1145/3726856.3726862, arXiv:2504.04416v1 (Theorem 5.4, Section 5.1.2, and Open Problem 5.3 defining the sentence PNP[g]).
