# xSAT lies in promise-NP ∩ promise-coNP

Let $\mathrm{xSAT}$ be the promise problem whose instances are pairs $(\varphi_1,\varphi_2)$ of CNF formulas exactly one of which is satisfiable, the yes-instances being those with $\varphi_1$ satisfiable. Then $\mathrm{xSAT}\in\mathrm{promise}\text{-}\mathsf{NP}\cap\mathrm{promise}\text{-}\mathsf{coNP}$, although $\mathrm{xSAT}$ is $\mathsf{NP}$-hard under Cook reductions to promise problems.

## Proof sketch

A satisfying assignment of $\varphi_1$ certifies a yes-instance and one of $\varphi_2$ certifies a no-instance; the separating languages are $\{(\varphi_1,\varphi_2):\varphi_1\in\mathrm{SAT}\}\in\mathsf{NP}$ and $\{(\varphi_1,\varphi_2):\varphi_2\notin\mathrm{SAT}\}\in\mathsf{coNP}$.

## Depends on

- [Promise problems and promise classes](promise-problems.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The class coNP](../../../complexity-classes/the-classes-p-np-and-conp/co-np.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 0–2", 2006, Exercise 2.36.
- Oded Goldreich, "On Promise Problems: A Survey", Theoretical Computer Science: Essays in Memory of Shimon Even, 2006.
