# Feasible instances of 2-DIMENSIONAL CONSECUTIVE SETS

An instance $(s, C)$ of 2-DIMENSIONAL CONSECUTIVE SETS, where $C$ is a list of lists $\Sigma_1, \dots, \Sigma_n$ of natural numbers, is feasible when there is a function $g : \mathbb{N} \to \mathbb{N}$, read as putting each symbol $x$ into the set $X_{g(x)}$ (indices start at $0$, and empty sets are allowed), such that for every list $\Sigma_j$ in $C$:

- $g$ takes distinct values on the distinct symbols occurring in $\Sigma_j$; and
- there is a natural number $l$ with $l \le g(x) < l + \operatorname{length}(\Sigma_j)$ for every entry $x$ of $\Sigma_j$.

The window $[l, l + \operatorname{length}(\Sigma_j))$ has the length of the list $\Sigma_j$, counting repeated entries, not the number of distinct symbols in it. For example, the lists $[0,1]$, $[1,2]$, $[0,0,2]$ are feasible with $g$ the identity: the window $[0,3)$ of the last list has length three. When $\Sigma_j$ has no repeated entries, its length is $|\Sigma_j|$, and the condition says that the elements of $\Sigma_j$ lie in distinct sets among the $|\Sigma_j|$ consecutive sets $X_l, \dots, X_{l+|\Sigma_j|-1}$. Feasibility does not include well-formedness (it neither excludes repeated entries nor requires symbols below $s$); the decision problem requires both.
