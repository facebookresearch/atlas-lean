# Lynch: languages outside P have infinite polynomial complexity cores

Let $\mathcal{C}$ be a countable class of sets containing all finite sets and closed under finite unions, and let $A\notin\mathcal{C}$. Then $A$ has an infinite complexity core for $\mathcal{C}$. For $\mathcal{C}=\mathsf{P}$ Lynch proves an effective version with cores defined by running times: every recursive $A\notin\mathsf{P}$ has an infinite recursive polynomial complexity core, i.e. an infinite recursive set $X$ such that for every machine $M$ deciding $A$ and every polynomial $p$, $M$ runs for more than $p(|x|)$ steps on all but finitely many $x\in X$.

## Proof sketch

Enumerate $\mathcal{C}=\{C_1,C_2,\dots\}$ and build $X$ in stages: at stage $s$ add a new string lying outside $U_s=\bigcup\{C_i : i\le s,\ C_i\subseteq A\text{ or }C_i\subseteq\overline{A}\}$. Such a string exists, since otherwise $A$ would be the union of the sets $C_i\subseteq A$ with $i\le s$ and a finite set, hence in $\mathcal{C}$. Each $C_i$ contained in $A$ or $\overline{A}$ then meets $X$ only in strings added before stage $i$. This construction is not effective; Lynch's recursive core for $\mathsf{P}$ comes from a clocked simulation of all machines against a decider for $A$.

## Depends on

- [P-immune and P-bi-immune sets; complexity cores](p-immune-sets-and-cores.md)

## Sources

- Nancy Lynch, "On reducibility to complex or sparse sets", Journal of the ACM 22(3), 1975.
