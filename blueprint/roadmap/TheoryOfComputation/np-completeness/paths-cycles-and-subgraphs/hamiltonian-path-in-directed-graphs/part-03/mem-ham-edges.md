# Arcs of the Hamiltonian path construction

Let $\varphi$ be a CNF formula with clauses
$C_0, \dots, C_{m-1}$ and distinct variables $x_0, \dots, x_{k-1}$ (in the order the
construction lists them), and write $T(i) = m + i(3m + 2)$ for the top of diamond $i$ and
$R(i, l) = T(i) + 1 + l$ for its row vertex $l$. Then $(u, v)$ is an arc of the Hamiltonian path
instance of $\varphi$ if and only if there is an $i < k$ such that $(u, v)$ is one of the frame
arcs $(T(i), R(i, 0))$, $(T(i), R(i, 3m))$, $(R(i, 0), T(i + 1))$ and $(R(i, 3m), T(i + 1))$;
or $(u, v)$ is a row arc $(R(i, l), R(i, l + 1))$ or $(R(i, l + 1), R(i, l))$ for some
$l < 3m$; or, for some $j < m$, either $C_j$ contains the literal $x_i$ and $(u, v)$ is
$(R(i, 3j + 1), j)$ or $(j, R(i, 3j + 2))$, or $C_j$ contains the literal $\lnot x_i$ and
$(u, v)$ is $(R(i, 3j + 2), j)$ or $(j, R(i, 3j + 1))$.
