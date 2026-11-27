# Optimal POVMs for linear objectives and their dual certificates

Let $A$ be a finite nonempty set and $(H_a)_{a\in A}$ positive semidefinite matrices on $\mathbb{C}^\iota$.

1. (Weak duality) If $Z$ is positive semidefinite with $H_a\le Z$ for all $a$, then $\sum_a\operatorname{Re}\operatorname{Tr}(E_aH_a)\le\operatorname{Tr}Z$ for every family of positive semidefinite $E_a$ with $\sum_a E_a\le I$.
2. (Attainment and certificate) There are a POVM $(T_a)$ and a positive semidefinite $Z$ with $H_a\le Z$ for all $a$, complementary slackness $T_aZ = T_aH_a$ for all $a$, and $\sum_a\operatorname{Tr}(T_aH_a) = \operatorname{Tr}Z$. In particular the maximum of $\sum_a\operatorname{Tr}(E_aH_a)$ over POVMs equals $\min\{\operatorname{Tr}Z : Z\ge H_a\ \forall a\}$.

## Proof sketch

Weak duality: $\operatorname{Tr}(E_aH_a)\le\operatorname{Tr}(E_aZ)$ and $\sum_a\operatorname{Tr}(E_aZ)\le\operatorname{Tr}Z$. The set of POVMs is compact, so a maximizer $T$ exists; perturbing $T$ within the set of POVMs and using first-order optimality produces an operator $Z$ dominating every $H_a$ whose slack each optimal effect annihilates, which forces equality in weak duality.

## Depends on

- [Positive-operator-valued measurements and the Born rule](povm-and-born-rule.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "Quantum soundness of the classical low individual degree test", arXiv:2009.12982, 2020.
- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
