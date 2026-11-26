# Ren–Santhanam–Wang: Avoid for AC0 or NC0_4 with small stretch implies NC1 lower bounds

Solving $\mathcal{C}$-Avoid would give breakthrough lower bounds even for very weak $\mathcal{C}$:

1. an algorithm for $\mathrm{AC}^0$-Avoid with polynomial stretch ($m=\mathrm{poly}(n)$) implies lower bounds against $\mathrm{NC}^1$;
2. an algorithm for $\mathrm{NC}^0_4$-Avoid with very small stretch $m=n+n^{o(1)}$ implies lower bounds against $\mathrm{NC}^1$ and against branching programs.

Also, Avoid is in $\mathrm{FNP}$ if and only if there is a propositional proof system that breaks every non-uniform proof complexity generator.

## Proof sketch

A non-image of a suitable map from small $\mathrm{NC}^1$ circuits (or branching programs) to strings encodes a function outside the class; the work is to compute such a map, after adding auxiliary encodings of the computation to its input, by $\mathrm{AC}^0$ circuits with polynomial stretch or by $\mathrm{NC}^0_4$ circuits with stretch $n^{o(1)}$. The proof complexity statement identifies a non-uniform proof complexity generator with an Avoid instance and an $\mathrm{FNP}$ solution with a short proof that a string is outside its range.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)

## Proof depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)

## Sources

- Hanlin Ren, Rahul Santhanam and Zhikun Wang, "On the Range Avoidance Problem for Circuits", FOCS (2022), ECCC TR22-048.
