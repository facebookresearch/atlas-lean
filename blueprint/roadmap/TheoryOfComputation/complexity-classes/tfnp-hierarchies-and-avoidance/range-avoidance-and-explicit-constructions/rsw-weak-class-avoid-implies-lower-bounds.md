# Ren–Santhanam–Wang: Avoid for AC0 or NC0_4 with small stretch implies NC1 lower bounds

Solving $\mathcal{C}$-Avoid would give breakthrough lower bounds even for very weak $\mathcal{C}$:

1. if $\mathrm{AC}^0$-Avoid with stretch $\ell(n)$, for a small enough quasi-polynomial $\ell$, is solvable in $\mathrm{FP}^{\mathrm{NP}}$, then $\mathrm{E}^{\mathrm{NP}}\not\subseteq\mathrm{NC}^1$;
2. if $\mathrm{NC}^0_4$-Avoid with stretch $\ell(n)=n+n^{o(1)}$ is solvable in $\mathrm{FP}^{\mathrm{NP}}$, then $\mathrm{E}^{\mathrm{NP}}$ has neither subexponential-size formulas nor subexponential-size parity branching programs.

Also, Avoid is in $\mathrm{FNP}$ if and only if there is a propositional proof system that breaks every non-uniform proof complexity generator.

## Proof sketch

A non-image of a suitable map from small $\mathrm{NC}^1$ circuits (or branching programs) to strings encodes a function outside the class; the work is to compute such a map, after adding auxiliary encodings of the computation to its input, by $\mathrm{AC}^0$ circuits with quasi-polynomial stretch or by $\mathrm{NC}^0_4$ circuits with stretch $n^{o(1)}$. The proof complexity statement identifies a non-uniform proof complexity generator with an Avoid instance and an $\mathrm{FNP}$ solution with a short proof that a string is outside its range.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)

## Sources

- Hanlin Ren, Rahul Santhanam and Zhikun Wang, "On the Range Avoidance Problem for Circuits", FOCS (2022), ECCC TR22-048.
