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

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 10.26 (numbering of the 2007 public draft; "simple" ensembles there are the polynomial-time computable ones).
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 18 (Chapter 15, Exercise 4 of the January 2007 web draft).
