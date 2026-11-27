# P-immune and P-bi-immune sets; complexity cores

For a class $\mathcal{C}$ of sets, an infinite set $A$ is **$\mathcal{C}$-immune** if it has no infinite subset in $\mathcal{C}$, and **$\mathcal{C}$-bi-immune** if both $A$ and $\overline{A}$ are $\mathcal{C}$-immune. A set $X$ is a **complexity core** of $A$ for $\mathcal{C}$ if every $B\in\mathcal{C}$ with $B\subseteq A$ or $B\subseteq\overline{A}$ has $B\cap X$ finite. For a class $\mathcal{C}$ containing all cofinite sets (such as $\mathsf{P}$), $A$ is $\mathcal{C}$-bi-immune iff $\{0,1\}^*$ is a complexity core of $A$; for other classes the condition on $\{0,1\}^*$ does not force $A$ and $\overline{A}$ to be infinite (for the class of finite sets, $\{0,1\}^*$ is a complexity core of the empty set). For $\mathcal{C}=\mathsf{P}$ these are the polynomial-time analogues of immune sets in computability.

## Depends on

- [Immune set](../../../degrees-and-hierarchies/productive-creative-simple-and-immune-sets/immune.md)
- [The complexity class P](../../the-classes-p-np-and-conp/p.md)

## Sources

- José L. Balcázar and Uwe Schöning, "Bi-immune sets for complexity classes", Mathematical Systems Theory 18(1), 1985.
- Nancy Lynch, "On reducibility to complex or sparse sets", Journal of the ACM 22(3), 1975.
