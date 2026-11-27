# Evaluation of FO + TC formulas

Fix an ordered graph with domain
$D = \{0, \dots, n - 1\}$, an assignment $\rho$ of an element of $D$ to each variable index and
an assignment $S$ of a relation on lists of elements of $D$ to each relation symbol. The truth
value of a formula is defined by recursion. The equation between variables $i$ and $j$ holds
when $\rho(i) = \rho(j)$. Relation symbol $i$ applied to variables $j_1, \dots, j_k$ holds when
$S_i$ holds of the list $[\rho(j_1), \dots, \rho(j_k)]$. Negation, conjunction and disjunction
are interpreted as usual. An existential formula $\exists \varphi$ holds when $\varphi$ holds
under the assignment sending $0$ to some $d \in D$ and $j + 1$ to $\rho(j)$. A transitive
closure $\mathrm{TC}(\varphi; \bar u, \bar v)$ is false when the index lists $\bar u$ and
$\bar v$ have different lengths. Otherwise, with $a$ their common length, it holds when the
tuple $(\rho(v_0), \dots, \rho(v_{a-1}))$ is reachable from $(\rho(u_0), \dots, \rho(u_{a-1}))$
in zero or more steps, where a step from $s \in D^a$ to $t \in D^a$ means that $\varphi$ holds
under the assignment sending $j < a$ to $s_j$, $a \le j < 2a$ to $t_{j - a}$, and $j \ge 2a$ to
$\rho(j - 2a)$.
