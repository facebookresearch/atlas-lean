# Black-box separations PLS^dt ⊄ PPADS^dt and SOPL^dt ⊄ PPA^dt

$\mathsf{PLS}^{dt}\not\subseteq\mathsf{PPADS}^{dt}$ and $\mathsf{SOPL}^{dt}\not\subseteq\mathsf{PPA}^{dt}$. Consequently there are oracles $\mathcal O$ with $\mathsf{PLS}^{\mathcal O}\not\subseteq\mathsf{PPADS}^{\mathcal O}$ and $\mathsf{SOPL}^{\mathcal O}\not\subseteq\mathsf{PPA}^{\mathcal O}$.

## Proof sketch

By the characterizations, $S(F)\in\mathsf{PLS}^{dt}$ means short narrow Resolution and $S(F)\in\mathsf{PPADS}^{dt}$ means short low-degree uSA; the formulas of the Resolution versus uSA separation therefore give a problem in $\mathsf{PLS}^{dt}\setminus\mathsf{PPADS}^{dt}$. Similarly $\mathsf{SOPL}^{dt}$ is RevRes and $\mathsf{PPA}^{dt}$ is $\mathbb F_2$-NS, so the RevRes versus Nullstellensatz separation gives the second claim. Black-box separations relativize to oracle separations.

## Depends on

- [Query total search problems TFNP^dt, decision-tree formulations and the black-box classes](query-tfnp-and-formulations.md)

## Proof depends on

- [Resolution is not simulated by unary Sherali–Adams: low-degree simulations need exponentially large coefficients](resolution-not-simulated-by-unary-sherali-adams.md)
- [Reversible Resolution is not simulated by Nullstellensatz over any field](reversible-resolution-not-simulated-by-nullstellensatz.md)
- [Göös–Kamath–Robere–Sokolov: PPA^dt is characterized by Nullstellensatz degree over F2](ppa-dt-characterized-by-f2-nullstellensatz.md)
- [Göös et al.: PPAD^dt, PPADS^dt, SOPL^dt and EOPL^dt are characterized by uNS, uSA, RevRes and RevResT](ppad-ppads-sopl-eopl-proof-system-characterizations.md)
- [PLS^dt is characterized by Resolution: PLS^dt(S(F)) = Θ(Res(F))](pls-dt-characterized-by-resolution.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
