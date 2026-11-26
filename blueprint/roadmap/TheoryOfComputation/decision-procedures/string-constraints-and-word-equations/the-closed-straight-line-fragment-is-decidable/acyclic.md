# Acyclic closed straight-line system

String terms over an alphabet $\alpha$ with variables $x_0, x_1, \dots$ (indexed by $\mathbb{N}$) are built from constant words, variables, concatenation and letter-to-word morphisms; $\sigma(t)$ denotes the value of a term $t$ under an assignment $\sigma : \mathbb{N} \to \alpha^*$ of words to the variables, and string formulas are positive Boolean combinations (conjunction, disjunction, true, false) of atoms (term equations, regular memberships, length bounds). A closed straight-line system $S$ consists of a finite list of defining terms $t_0, \dots, t_{m-1}$ ($t_k$ defines $x_k$) and a query formula $\varphi$. The system $S$ is acyclic if every defining term $t_k$ mentions only earlier variables (every
variable $x_j$ occurring in $t_k$ has $j < k$) and the query mentions only defined variables (every variable
$x_j$ occurring in $\varphi$ has $j < m$).

Then every variable occurring anywhere in the system is defined, and substituting the definitions repeatedly ends with
ground terms: there are no free input variables.
