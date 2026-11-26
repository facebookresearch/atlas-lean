# Lynch: languages outside P have infinite polynomial complexity cores

Let $\mathcal{C}$ be a countable class of sets containing all finite sets and closed under finite unions, and let $A\notin\mathcal{C}$. Then $A$ has an infinite complexity core for $\mathcal{C}$; if $\mathcal{C}$ is recursively presentable (e.g. $\mathsf{P}$) and $A$ is recursive, the core can be taken recursive. In particular every recursive $A\notin\mathsf{P}$ has an infinite polynomial complexity core: an infinite set $X$ such that every machine deciding $A$ runs in super-polynomial time on all but finitely many elements of $X$.

## Proof sketch

Enumerate $\mathcal{C}=\{C_1,C_2,\dots\}$; build $X$ in stages, adding at stage $s$ a string on which none of the finitely many $C_i\subseteq A$ or $\subseteq\overline{A}$ with $i\le s$ is correct-and-contained; such strings exist because $A\notin\mathcal{C}$ and $\mathcal{C}$ is closed under finite unions and finite variations.

## Depends on

- [P-immune and P-bi-immune sets; complexity cores](p-immune-sets-and-cores.md)

## Sources

- Nancy Lynch, "On reducibility to complex or sparse sets", Journal of the ACM 22(3), 1975.
