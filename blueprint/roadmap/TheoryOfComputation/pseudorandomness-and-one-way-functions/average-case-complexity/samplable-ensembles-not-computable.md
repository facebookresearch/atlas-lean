# Unless #P ⊆ FP, some samplable ensemble is not polynomial-time computable

If $\#\mathsf{P}\not\subseteq\mathsf{FP}$ (equivalently $\mathsf{P}\ne\mathsf{P}^{\#\mathsf{P}}$), then $\mathsf{PSamp}\not\subseteq\mathsf{PComp}$: there is a polynomial-time samplable ensemble whose cumulative distribution function is not polynomial-time computable.

## Proof sketch

Take the ensemble that samples a random pair $(\varphi,a)$ and outputs $\varphi$ followed by an indicator of whether $a$ satisfies $\varphi$, suitably ordered. Its cumulative distribution at a boundary point reveals $\#\varphi$, so computing it in polynomial time would give $\#\mathrm{SAT}\in\mathsf{FP}$.

## Depends on

- [Distributional problems, DistNP, AvgP and HeurP](distributional-problems.md)
- [The counting class $\#P$](../../complexity-classes/time-and-space-complexity-classes/sharp-p.md)

## Proof depends on

- [Counting SAT is #P-complete](../../counting-complexity/counting-satisfiability-sat/count-sat-sharp-p-complete.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 9–10", 2007, Exercise 10.26.
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Chapter 15, Exercise 4.
