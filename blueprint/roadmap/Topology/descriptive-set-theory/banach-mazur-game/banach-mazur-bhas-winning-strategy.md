# Winning strategy for the second player in the Banach–Mazur game

Let
$E \subseteq \mathbb{R}$. In this game a move is a pair of reals $(c, d)$, standing for the open
interval $(c, d)$, and a valid strategy is a map from pairs to pairs answering each pair $(c, d)$
with $c < d$ by a pair $(c', d')$ with $c \le c' < d' \le d$. Player B has a winning strategy for
$E$ if there is a valid strategy $\sigma_B$ such that, for all reals $a < b$ and every valid
strategy $\sigma_A$, the play $(c_n, d_n)_{n \ge 0}$ given by $(c_0, d_0) = (a, b)$,
$(c_{n+1}, d_{n+1}) = \sigma_B(c_n, d_n)$ for even $n$ and
$(c_{n+1}, d_{n+1}) = \sigma_A(c_n, d_n)$ for odd $n$ satisfies
$\left(\bigcap_{n} (c_n, d_n)\right) \cap E = \emptyset$.
