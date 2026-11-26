# The NPA semidefinite hierarchy converges to the commuting-operator value

For every game $G$ there is a sequence of semidefinite programs, computable from $G$, with optimal values $\omega_1(G) \ge \omega_2(G) \ge \cdots \ge \omega^{co}(G)$ and $\lim_k \omega_k(G) = \omega^{co}(G)$. Consequently the set of games with $\omega^{co}(G) < 1/2$ is recursively enumerable, i.e. the promise problem "$\omega^{co}(G) = 1$ versus $\omega^{co}(G) < 1/2$" lies in $\mathrm{coRE}$.

## Proof sketch

Level $k$ optimizes over moment matrices indexed by words of length at most $k$ in the measurement operators, positive semidefinite and satisfying the projection and commutation relations. Feasible points dominate every commuting-operator strategy. A limit of feasible moment sequences defines, via the GNS construction, a commuting-operator strategy, giving convergence. Semidefinite programs can be solved to any precision, so a level certifying a value below $1/2$ is found whenever one exists.

## Depends on

- [Quantum correlation sets C_q, C_qs, C_qa and C_qc](quantum-correlation-sets-q-qs-qa-qc.md)

## Proof depends on

- [Containments C_q in C_qs in C_qa in C_qc and closedness of C_qc](containments-and-closedness-of-correlation-sets.md)

## Sources

- Miguel Navascues, Stefano Pironio, Antonio Acin, "A convergent hierarchy of semidefinite programs characterizing the set of quantum correlations", New Journal of Physics 10 (2008); arXiv:0803.4290.
