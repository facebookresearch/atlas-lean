# PV does not prove superpolynomial extended Frege lower bounds

The Krajíček–Pudlák theorem, in Oliveira's exposition: Cook's theory $\mathsf{PV}$ cannot prove that there are arbitrarily large tautologies without extended Frege proofs of size $n^{\log n}$, so superpolynomial EF lower bounds are not provable by polynomial-time reasoning.

Let $\mathsf{Sat}(x, y)$ be a quantifier-free $\mathcal{L}_{\mathsf{PV}}$-formula expressing that $y$ satisfies the propositional formula $x$, let $\mathsf{Taut}(x) = \forall y \le x\ \mathsf{Sat}(x, y)$, and let $\mathsf{Prf}_{\mathsf{EF}}(x, z)$ express that $z$ is an $\mathsf{EF}$-proof of $x$. The sentence

$$
\Psi_{\mathsf{EF}} = \forall x\ \exists \phi \ge x\ \big[\mathsf{Taut}(\phi) \wedge \forall \pi\ \big(|\pi| \le |\phi| \# |\phi| \rightarrow \neg \mathsf{Prf}_{\mathsf{EF}}(\phi, \pi)\big)\big]
$$

is not provable in $\mathsf{PV}$. Here $|\phi| \# |\phi| = 2^{||\phi|| \cdot ||\phi||}$ is of order $n^{\log n}$ for $n = |\phi|$, and the proof works for any reasonable formalization of a superpolynomial size bound.

## Proof sketch

The proof is model-theoretic. In a model $M$ of $\mathsf{PV}$, a formula has no $\mathsf{EF}$-proof exactly when some extension of $M$ satisfying $\mathsf{PV}$ falsifies it, by compactness and the $\mathsf{PV}$-provable correctness of Cook's translation. Iterating this while taking cuts gives a countable model $M^*$ in which every tautology has an $\mathsf{EF}$-proof and in which every element has length at most $n^k$, $k$ standard, for some nonstandard length $n = |a|$. If $\mathsf{PV} \vdash \Psi_{\mathsf{EF}}$, some tautology $\phi \ge a$ in $M^*$ has no $\mathsf{EF}$-proof of size $|\phi| \# |\phi|$, yet it has one of size $n^k \le n \# n$, a contradiction.

## Depends on

- [Cook's theory PV of polynomial-time reasoning](../bounded-arithmetic-and-witnessing/cooks-theory-pv.md)
- [Cook–Reckhow propositional proof systems](../../../../Logic/propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

- [Compactness theorem for first-order logic](../../../../Logic/model-theory/compactness-theorem-for-first-order-logic.md)
- [Soundness for theories](../../../../Logic/first-order-logic/first-order-natural-deduction/models.md)

## Sources

- Igor C. Oliveira, "SIGACT News Complexity Theory Column 124: Meta-Mathematics of Computational Complexity Theory", *ACM SIGACT News* 56(1), 2025, DOI 10.1145/3726856.3726862, arXiv:2504.04416v1 (Theorem 5.13, Section 5.2.2, credited there to Krajíček and Pudlák, with Lemmas 5.9, 5.10, 5.12 and Fact 5.11).
- Jan Krajíček and Pavel Pudlák, "Propositional provability and models of weak arithmetic", in *CSL '89*, Lecture Notes in Computer Science 440, Springer, 1990, pp. 193–210, DOI 10.1007/3-540-52753-2_40.
