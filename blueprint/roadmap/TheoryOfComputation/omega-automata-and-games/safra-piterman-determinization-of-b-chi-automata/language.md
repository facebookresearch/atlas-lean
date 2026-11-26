# Language of a deterministic parity automaton

Let $(s_0, \delta, \Omega)$ be a deterministic parity automaton over states $S$ and alphabet $\Sigma$. Its language is the set of infinite words $x : \mathbb{N} \to \Sigma$ such that, for the run $\rho$ on $x$, the priority sequence $\Omega(\rho(0)), \Omega(\rho(1)), \dots$ satisfies the even max-parity condition: there is an even $d$ such that $\Omega(\rho(k)) = d$ for infinitely many $k$ and every value taken infinitely often is at most $d$.
