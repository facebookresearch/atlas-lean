# GR(1) synthesis

Let $G$ be a finite game structure with initial and transition constraints for environment and system and a GR(1) winning condition $\bigwedge_{i=1}^{m} \mathbf{GF}\, p_i \to \bigwedge_{j=1}^{n} \mathbf{GF}\, q_j$, where $m, n \ge 1$ and the $p_i$, $q_j$ are sets of states (a condition with no assumptions or no guarantees is brought to this form by adding the set of all states). The system wins the game, that is, for every initial input satisfying $\theta_e$ it can choose an initial output satisfying $\theta_s$ from whose resulting state it has a winning strategy, if and only if for every initial input satisfying $\theta_e$ there is such an initial output whose resulting state lies in the winning region computed by the nested fixpoint $\nu Z.\, \bigwedge_j \mu Y.\, \bigvee_i \nu X.\, \bigl((q_j \wedge \mathrm{Cpre}(Z)) \vee \mathrm{Cpre}(Y) \vee (\neg p_i \wedge \mathrm{Cpre}(X))\bigr)$, where $\mathrm{Cpre}$ is the controllable predecessor: $\mathrm{Cpre}(S)$ is the set of states from which, for every input allowed by the environment transition constraint, the system has an output allowed by its transition constraint leading into $S$ (the environment moves first in each step). In that case a winning strategy with memory of size $n$ can be extracted from the intermediate fixpoint iterates.

## Depends on

- [Realizability of specifications over infinite words](realizability-of-specifications-over-infinite.md)

## Proof depends on

- [Attractor](../parity-games/attractor.md)
- [The GR(1) winning region as a nested fixpoint](the-gr-1-winning-region-as-a-nested-fixpoint.md)

## Sources

- R. Bloem, B. Jobstmann, N. Piterman, A. Pnueli and Y. Sa'ar, "Synthesis of Reactive(1) designs", *Journal of Computer and System Sciences* 78(3):911–938, 2012, Section 2.3 (game structures and when a game is winning for the system), Section 3.2 (Lemma 2, Theorem 3 and the strategy construction from the stored iterates) and Section 4.1 (extracting the strategy), <https://www.cse.chalmers.se/~piterman/publications/2012/BJPPS12.pdf>
