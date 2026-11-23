# Correctness of the SAT-to-string-constraints translation

A CNF is a finite list of clauses, each a finite list of literals $(v, b)$ with $v \in \mathbb{N}$ a variable and $b \in \{0, 1\}$; it is satisfiable if some assignment $\nu : \mathbb{N} \to \{0, 1\}$ gives every clause a literal $(v, b)$ with $\nu(v) = b$. The string-constraint encoding of a CNF $\varphi = C_1 \cdots C_m$ is the formula over the alphabet $\{0, 1\}$ with variables $x_v$ ($v \in \mathbb{N}$) given by $\bigwedge_{j=1}^{m} \bigvee_{(v, b) \in C_j} (x_v = b)$, where $x_v = b$ is the word equation between the variable $x_v$ and the one-letter constant word $b$, an empty disjunction is false and an empty conjunction is true. For every CNF $\varphi$, $\varphi$ is satisfiable if and only if there is a substitution $\sigma$
of binary words for the variables with $|\sigma(x_v)| \le 1$ for all $v \in \mathbb{N}$ that satisfies the
string-constraint encoding of $\varphi$.
