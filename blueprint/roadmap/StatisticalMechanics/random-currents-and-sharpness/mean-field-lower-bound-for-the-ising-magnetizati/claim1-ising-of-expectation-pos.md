# Cluster lower bound for double-current sums

Let $G = (V, E)$ be a finite simple graph, $\beta \ge 0$ and $J_e \ge 0$ for every pair $e$, with $\langle \cdot \rangle_{\beta, J}$ the zero-field [Ising expectation with couplings](../random-currents-and-the-switching-lemma/expectation-j.md) $J$ and $\Sigma_P(A, B) = \sum_{\partial n_1 = A,\ \partial n_2 = B} w(n_1)\, w(n_2)\, \mathbf 1_{P(n_1 + n_2)}$ the [gated double-current sum](gated-source-pair-sum.md). Let $S \subseteq V$
and $o, x, y, g \in V$ with $o, x \notin S$, $y, g \in S$, $y \ne g$ and $\langle \sigma_y \sigma_g \rangle_{\beta, J} > 0$.
Writing $C(n)$ for the set of vertices not joined to $o$ by edges carrying positive current in $n$,

$$\Sigma_{C = S}\bigl(\{y, g\} \,\triangle\, \{o, x\},\ \emptyset\bigr) \ge \langle \sigma_y \sigma_g \rangle_{\beta, J}^{-1}\ \Sigma_{C = S,\ y \leftrightarrow g}\bigl(\{o, x\},\ \emptyset\bigr)$$

(M. Aizenman, D. J. Barsky and R. Fernández, *The phase transition in a general class of Ising-type models is sharp*, J. Stat. Phys. 47 (1987) 343–374).
