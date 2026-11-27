# Emptiness of blind alternating finite automata is undecidable

No algorithm decides, given a blind alternating finite automaton, whether some input is accepted with some certificate.

**Theorem.** The emptiness problem for [blind alternating finite automata](blind-alternating-finite-automata.md) is undecidable: there is no algorithm that, given a BAFA $B$, decides whether there exist an input $w$ and a certificate $c$ such that $B$ accepts $w$ with certificate $c$.

The input alphabet is part of the instance; the reduction uses inputs over $\{0,1,\kappa\}$ with a separator $\kappa$. Since blind alternation is a special case of private alternation, emptiness is also undecidable for realtime private alternating finite automata.

## Depends on

- [Blind alternating finite automata](blind-alternating-finite-automata.md)

## Proof depends on

- [Acceptance is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-accepts.md)

## Expansion

From a Turing machine $M$ and an input $x$, let $C_0,\dots,C_n\in\{0,1\}^*$ be the configurations of an accepting computation of $M$ on $x$, if there is one. The proof builds a BAFA $B$ that accepts only the input $\kappa\kappa C_0\kappa\kappa C_1\kappa\kappa\cdots\kappa\kappa C_n\kappa\kappa$, using the certificate $C_0\kappa C_1\kappa\cdots\kappa C_n$. At the start, $B$ splits universally into two branches. The first checks that the input and the certificate list the same configurations, block by block, starting from $C_0$ hard-wired in its states. The second checks, with the certificate one block behind the input, that each input block is a legal successor of the previous certificate block (the possible local changes of one step are finitely many windows), and that the last block is accepting. The doubled separators on the input leave room for the certificate head to lag. Every incorrect input is refuted on one branch for every certificate, so $L(B)\neq\emptyset$ exactly when $M$ accepts $x$. This reuses the comparison technique of the BAFA for $\{w2w\}$.

## Sources

- H. Gökalp Demirci, Mika Hirvensalo, Klaus Reinhardt, A. C. Cem Say and Abuzer Yakaryılmaz, "Alternating, private alternating, and quantum alternating realtime automata", *Logical Methods in Computer Science* 15(3), 2019, paper 22, doi:[10.23638/LMCS-15(3:22)2019](https://doi.org/10.23638/LMCS-15(3:22)2019); numbering of arXiv:1407.0334v5 ([arXiv](https://arxiv.org/abs/1407.0334v5)): Theorem 3.7 and its proof.
