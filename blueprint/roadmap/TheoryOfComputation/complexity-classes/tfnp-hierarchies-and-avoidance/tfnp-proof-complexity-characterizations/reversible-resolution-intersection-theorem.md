# Intersection theorems: Reversible Resolution is the intersection of Resolution and unary Sherali–Adams

For every unsatisfiable CNF formula $F$,

$$
\mathrm{RevRes}(F)=\Theta\bigl(\mathrm{Res}(F)+\mathrm{uSA}(F)\bigr),\qquad \mathrm{RevResT}(F)=\Theta\bigl(\mathrm{Res}(F)+\mathrm{uNS}(F)\bigr).
$$

Thus $F$ has a short, narrow Reversible Resolution refutation if and only if it has both a short, narrow Resolution refutation and a short, low-degree unary Sherali–Adams refutation, and similarly for RevResT with unary Nullstellensatz.

## Proof sketch

Recall the black-box collapses $\mathsf{SOPL}=\mathsf{PLS}\cap\mathsf{PPADS}$ and $\mathsf{EOPL}=\mathsf{PLS}\cap\mathsf{PPAD}$ (which hold for decision-tree formulations with polynomial loss). Convert a Resolution proof into a $\mathsf{PLS}^{dt}$ formulation of $S(F)$ and a uSA proof into a $\mathsf{PPADS}^{dt}$ formulation, apply the collapse to obtain a $\mathsf{SOPL}^{dt}$ formulation, and convert it back into a RevRes proof by the characterization; the other direction is immediate since RevRes is simulated by both systems. Göös et al. note that they see no direct proof-theoretic argument.

## Depends on

- [Reversible Resolution: a MaxSAT-style fragment of Resolution with consumed premises](reversible-resolution.md)
- [Unary Nullstellensatz and unary Sherali–Adams refutations of CNF formulas](unary-nullstellensatz-and-unary-sherali-adams.md)
- [Resolution refutation](../../../../Logic/propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Width of a derivation](../../../../Logic/propositional-logic/resolution-size-and-width/derivation-width.md)

## Proof depends on

- [Göös et al.: PPAD^dt, PPADS^dt, SOPL^dt and EOPL^dt are characterized by uNS, uSA, RevRes and RevResT](ppad-ppads-sopl-eopl-proof-system-characterizations.md)
- [PLS^dt is characterized by Resolution: PLS^dt(S(F)) = Θ(Res(F))](pls-dt-characterized-by-resolution.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
