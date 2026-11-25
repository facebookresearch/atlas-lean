# Run of a deterministic parity automaton

Let $(s_0, \delta, \Omega)$ be a deterministic parity automaton over states $S$ and alphabet $\Sigma$, and let $x : \mathbb{N} \to \Sigma$ be an infinite word. The run of the automaton on $x$ is the sequence $\rho : \mathbb{N} \to S$ given by

$$\rho(0) = s_0, \qquad \rho(k + 1) = \delta\bigl(\rho(k), x(k)\bigr).$$
