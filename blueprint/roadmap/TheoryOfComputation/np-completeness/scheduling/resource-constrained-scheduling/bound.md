# Resource bound in RESOURCE CONSTRAINED SCHEDULING

An instance of RESOURCE CONSTRAINED SCHEDULING is a tuple $(m, r, B, T, D)$ of a number $m$ of processors, a number $r$ of resources, a list $B = (B_0, \dots, B_{r-1})$ of resource bounds, a list $T$ of rows, the row of task $t$ being $(R_0(t), \dots, R_{r-1}(t))$, and a deadline $D$. For a natural number $k$, the bound $B_k$ of resource $k$ is the entry of $B$ at position $k$, and $0$ when $B$ has no entry at position $k$. That $B$ has exactly $r$ entries, each positive, is a condition of a well-formed instance, not of this definition.
