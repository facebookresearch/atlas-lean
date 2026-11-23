# Simon–Lieb inequality on a finite graph

Let $G = (V, E)$ be a finite simple graph, $\beta \ge 0$ and $J_e \ge 0$ for every pair $e$, with $\langle \sigma_a \sigma_b \rangle_{\beta, J}$ the [two-point function](two-point-j.md) with couplings $J$ (equal to $1$ when $a = b$). For $S \subseteq V$, $o \in S$ and $z \notin S$,

$$\langle \sigma_o \sigma_z \rangle_{\beta, J} \le \sum_{x \in S} \sum_{y \in V \setminus S} \tanh(\beta J_{xy})\, \langle \sigma_o \sigma_x \rangle_{\beta, J|_S}\, \langle \sigma_y \sigma_z \rangle_{\beta, J},$$

with $J|_S$ the [coupling restricted to $S$](../mean-field-lower-bound-for-the-ising-magnetizati/coupling-in.md) (B. Simon, *Correlation inequalities and the decay of correlations in ferromagnets*, Comm. Math. Phys. 77 (1980) 111–126; E. H. Lieb, *A refinement of Simon's correlation inequality*, Comm. Math. Phys. 77 (1980) 127–135).
