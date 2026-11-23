# Closed straight-line system

String terms over an alphabet $\alpha$ with variables $x_0, x_1, \dots$ (indexed by $\mathbb{N}$) are built from constant words, variables, concatenation and letter-to-word morphisms; $\sigma(t)$ denotes the value of a term $t$ under an assignment $\sigma : \mathbb{N} \to \alpha^*$ of words to the variables, and string formulas are positive Boolean combinations (conjunction, disjunction, true, false) of atoms (term equations, regular memberships, length bounds). A closed straight-line system over $\alpha$ consists of a finite list of terms $t_0, \dots, t_{m-1}$, the
defining term $t_k$ being the definition of the variable $x_k$, together with a query formula $\varphi$.
This is only the raw data: a term or the query may mention any variable, including $x_j$ with $j \ge k$ in
$t_k$ (a forward reference) or with $j \ge m$ (an undefined variable). The condition that $t_k$ mentions only
$x_j$ with $j < k$ and $\varphi$ only $x_j$ with $j < m$ is the separate acyclicity condition.
