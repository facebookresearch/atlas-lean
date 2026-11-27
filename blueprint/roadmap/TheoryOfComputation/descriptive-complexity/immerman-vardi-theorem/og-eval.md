# Evaluation of FO + LFP formulas in an ordered graph

Let $G$ be an ordered graph with
vertex set $V = \{0, \dots, n - 1\}$, let $\rho$ assign a vertex to each variable
$0, 1, 2, \dots$, and let $S$ assign to each relation symbol $i$ a predicate $S_i$ on lists of
vertices. The truth of a formula is defined by recursion: $x_a = x_b$ holds when
$\rho(a) = \rho(b)$; the atom $R_i(x_{a_1}, \dots, x_{a_k})$ holds when $S_i$ holds of
$(\rho(a_1), \dots, \rho(a_k))$; negation, conjunction and disjunction are evaluated as usual;
$\exists \varphi$ holds when $\varphi$ holds for some $v \in V$ under the assignment sending
variable $0$ to $v$ and variable $j + 1$ to $\rho(j)$. The least-fixed-point formula with bound
symbol $R$, arity $k$, body $\varphi$ and argument variables $a_1, \dots, a_m$ holds when
$(\rho(a_1), \dots, \rho(a_m))$ lies in $X_{n^k}$, where $X_0$ is empty and a list $t$ lies in
$X_{s+1}$ when $\varphi$ holds with $R$ reinterpreted as $X_s$ (the other symbols keeping their
interpretation under $S$) and with variable $j$ assigned the $j$-th entry of $t$ (or $\rho(0)$
if $t$ has no such entry) for $j < k$ and $\rho(j - k)$ for $j \ge k$.
