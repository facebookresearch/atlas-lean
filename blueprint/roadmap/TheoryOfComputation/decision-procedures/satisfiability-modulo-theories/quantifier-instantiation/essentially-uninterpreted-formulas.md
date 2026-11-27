# Essentially uninterpreted formulas

Fix a background theory $T$ whose symbols are *interpreted*, and let $F$ be a set of clauses $C_1, \dots, C_m$ that may also contain *uninterpreted* function and predicate symbols. $F$ is *essentially uninterpreted* if every variable occurs only as an argument of uninterpreted symbols. Introduce a set variable $S_{k,i}$ for each variable $x_i$ of each clause $C_k$ and $A_{f,j}$ for each argument position $j$ of each uninterpreted $f$. The system $\Delta_F$ of set constraints has, for each occurrence of $f$ in $C_k$ whose $j$-th argument is

- a ground term $t$: the constraint $t \in A_{f,j}$;
- a non-ground term $t[x_1, \dots, x_n]$ other than a variable: $t[S_{k,1}, \dots, S_{k,n}] \subseteq A_{f,j}$;
- a variable $x_i$: $S_{k,i} = A_{f,j}$.

Augment $\Delta_F$, for every set variable that its least solution leaves empty, by a constraint $a \in A_{f,j}$ (or $a \in S_{k,i}$) for a constant $a$ of the right sort, a fresh constant if there is none, and take the least solution of the augmented system, in which every set is nonempty. Without this step the least solution can be empty: for the clauses $P(x)$ and $\neg P(y)$ it gives no instance at all. The seed must be a constant, not an arbitrary ground term: with the clauses $P(x)$ and $Q(g(b))$ and the constants $a$ and $b$, the seed $g(a)$ for the set of $x$ would give the instance $P(g(a))$ although $a$ is not in the set for the argument of $g$, which the projection lemma for the instantiation needs. Let $F^*$ be the set of ground instances $C_k[S_{k,1}, \dots, S_{k,n_k}]$ of the clauses, where $n_k$ is the number of variables of $C_k$ and the variables are instantiated by terms from their sets. $F$ is in the *finite essentially uninterpreted fragment* if every $S_{k,i}$ is finite. $\Delta_F$ is *stratified* if a level function on set variables gives $S_{k,j}$ and $A_{f,i}$ the same level for each constraint $S_{k,j} = A_{f,i}$, and gives $A_{f,j}$ a smaller level than each $S_{k,i}$ in a constraint $t[S_{k,1}, \dots, S_{k,n}] \subseteq A_{f,j}$.

For example, $f(g(x_1) + a) \le h(x_1) \vee p(f(x_1) + b, x_2)$, with $+$ and $\le$ arithmetic, is essentially uninterpreted.

## Sources

- Y. Ge and L. de Moura, "Complete instantiation for quantified formulas in satisfiability modulo theories", in *Computer Aided Verification (CAV 2009)*, LNCS 5643, Springer, 2009, pp. 306–320, <https://leodemoura.github.io/files/ci.pdf>, Section 3: the definition, Example 1, the set constraints $\Delta_F$ and their least solution, with extra constraints $a \in S$ for constants $a$ to make every set nonempty, and Proposition 1 and Lemma 1, which need every ground argument of an uninterpreted symbol to lie in its set, Example 2, the instantiation $F^*$, the fragment FEU and stratified systems.
