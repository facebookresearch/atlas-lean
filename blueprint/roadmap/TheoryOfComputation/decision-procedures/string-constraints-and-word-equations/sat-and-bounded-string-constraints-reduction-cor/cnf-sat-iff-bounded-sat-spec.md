# SAT iff the bounded-search specification holds of the encoding

A CNF is a finite list of clauses, each a finite list of literals $(v, b)$ with $v \in \mathbb{N}$ a variable and $b \in \{0, 1\}$; it is satisfiable if some assignment $\nu : \mathbb{N} \to \{0, 1\}$ gives every clause a literal $(v, b)$ with $\nu(v) = b$. The string-constraint encoding of a CNF $\varphi = C_1 \cdots C_m$ is the formula over the alphabet $\{0, 1\}$ with variables $x_v$ ($v \in \mathbb{N}$) given by $\bigwedge_{j=1}^{m} \bigvee_{(v, b) \in C_j} (x_v = b)$, where $x_v = b$ is the word equation between the variable $x_v$ and the one-letter constant word $b$, an empty disjunction is false and an empty conjunction is true. Let $\varphi$ be a CNF and let $vs$ be a finite list of natural numbers containing every $v$ such
that $x_v$ occurs in the encoding of $\varphi$. Then $\varphi$ is satisfiable if and only if the bounded
search with bound $1$ over $vs$ succeeds on the encoding of $\varphi$, that is, some assignment of binary
words of length at most $1$ to the variables $x_v$, $v$ in $vs$ (all other variables receiving the empty
word), satisfies the encoding.
