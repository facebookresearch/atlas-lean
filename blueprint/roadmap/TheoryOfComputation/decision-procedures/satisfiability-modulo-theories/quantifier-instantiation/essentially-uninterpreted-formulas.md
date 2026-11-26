# Essentially uninterpreted formulas

Fix a background theory $T$ whose symbols are *interpreted*, and let $F$ be a set of clauses $C_1, \dots, C_m$ that may also contain *uninterpreted* function and predicate symbols. $F$ is *essentially uninterpreted* if every variable occurs only as an argument of uninterpreted symbols. Introduce a set variable $S_{k,i}$ for each variable $x_i$ of each clause $C_k$ and $A_{f,j}$ for each argument position $j$ of each uninterpreted $f$. The system $\Delta_F$ of set constraints has, for each occurrence of $f$ in $C_k$ whose $j$-th argument is

- a ground term $t$: the constraint $t \in A_{f,j}$;
- a non-ground term $t[x_1, \dots, x_n]$ other than a variable: $t[S_{k,1}, \dots, S_{k,n}] \subseteq A_{f,j}$;
- a variable $x_i$: $S_{k,i} = A_{f,j}$.

Take the least solution of $\Delta_F$, with every set nonempty, and let $F^*$ be the set of ground instances $C_k[S_{k,1}, \dots, S_{k,m}]$ of the clauses, the variables instantiated by terms from their sets. $F$ is in the *finite essentially uninterpreted fragment* if every $S_{k,i}$ is finite. $\Delta_F$ is *stratified* if a level function on set variables gives $S_{k,j}$ and $A_{f,i}$ the same level for each constraint $S_{k,j} = A_{f,i}$, and gives $A_{f,j}$ a smaller level than each $S_{k,i}$ in a constraint $t[S_{k,1}, \dots, S_{k,n}] \subseteq A_{f,j}$.

For example, $f(g(x_1) + a) \le h(x_1) \vee p(f(x_1) + b, x_2)$, with $+$ and $\le$ arithmetic, is essentially uninterpreted.

## Sources

- Y. Ge and L. de Moura, "Complete instantiation for quantified formulas in satisfiability modulo theories", in *Computer Aided Verification (CAV 2009)*, LNCS 5643, Springer, 2009, pp. 306–320, <https://leodemoura.github.io/files/ci.pdf>, Section 3: the definition, Example 1, the set constraints $\Delta_F$ and their least solution, Example 2, the instantiation $F^*$, the fragment FEU and stratified systems.
