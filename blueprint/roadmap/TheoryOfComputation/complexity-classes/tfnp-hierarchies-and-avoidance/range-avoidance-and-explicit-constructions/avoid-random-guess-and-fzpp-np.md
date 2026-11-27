# Avoid is solved by a random guess with probability 1/2 and lies in FZPP^NP

For every instance $C\colon\{0,1\}^n\to\{0,1\}^m$ with $m>n$, a uniformly random $y\in\{0,1\}^m$ is a solution with probability $1-|\mathrm{Im}(C)|/2^m\ge 1/2$. Consequently Avoid is solvable by a zero-error probabilistic polynomial-time algorithm with an $\mathrm{NP}$ oracle ($\mathrm{FZPP}^{\mathrm{NP}}$): sample $y$, ask the oracle whether $\exists x\,C(x)=y$, and repeat until the answer is no. Different runs output different solutions, so this algorithm is far from pseudodeterministic.

## Proof sketch

The bound on the image is a counting argument, and the oracle query is an $\mathrm{NP}$ predicate in $(C,y)$. The expected number of trials is at most $2$.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)
- [ZPP](../../time-and-space-complexity-classes/zpp.md)
- [Polynomial time with an oracle](../../time-and-space-complexity-classes/pwith-oracle.md)

## Sources

- Robert Kleinberg, Oliver Korten, Daniel Mitropolsky and Christos Papadimitriou, "Total Functions in the Polynomial Hierarchy", ITCS (2021), LIPIcs 185.
- Surendra Ghentiyala, Zeyong Li and Noah Stephens-Davidowitz, "Range avoidance, Arthur-Merlin, and TFNP", ECCC TR25-210 (2025).
