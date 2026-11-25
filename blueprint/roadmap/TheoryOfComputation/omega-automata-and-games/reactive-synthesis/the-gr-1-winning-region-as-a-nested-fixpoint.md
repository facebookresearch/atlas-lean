# The GR(1) winning region as a nested fixpoint

For a finite game structure with GR(1) winning condition $\bigwedge_{i=1}^{m} \mathbf{GF}\, p_i \to \bigwedge_{j=1}^{n} \mathbf{GF}\, q_j$ with $m, n \ge 1$ (a condition with no assumptions or no guarantees is brought to this form by adding the set of all states), the set of states from which the system wins equals

$$\nu Z.\, \bigwedge_{j=1}^{n} \mu Y.\, \bigvee_{i=1}^{m} \nu X.\, \bigl((q_j \wedge \mathrm{Cpre}(Z)) \vee \mathrm{Cpre}(Y) \vee (\neg p_i \wedge \mathrm{Cpre}(X))\bigr),$$

where $\mathrm{Cpre}$ is the controllable predecessor defined below.

Here a game structure has input variables chosen by the environment and output variables chosen by the system, initial constraints $\theta_e$ (on inputs) and $\theta_s$, and transition constraints $\rho_e$ and $\rho_s$. In each step the environment first chooses an input allowed by $\rho_e$ and the system then chooses an output allowed by $\rho_s$; a finite play is won by the system exactly when the environment has no allowed input at its last state. $\mathrm{Cpre}(S)$ is the set of states $s$ such that for every input allowed by $\rho_e$ at $s$ there is an output allowed by $\rho_s$ for which the resulting state lies in $S$.

## Proof depends on

- [Attractor](../parity-games/attractor.md)

## Sources

- R. Bloem, B. Jobstmann, N. Piterman, A. Pnueli and Y. Sa'ar, "Synthesis of Reactive(1) designs", *Journal of Computer and System Sciences* 78(3):911–938, 2012, Section 2.3 (game structures, plays and winning), Section 3 (the µ-calculus over game structures and its controllable-predecessor operator) and Section 3.2 (Equation (3), Lemma 2, and the Figure 1 implementation, which iterates a single set variable $Z$), <https://www.cse.chalmers.se/~piterman/publications/2012/BJPPS12.pdf>
