# Careful cooperative rational synthesis with common resources

In careful cooperative rational synthesis, players move a token on a finite graph whose edges change shared integer resources;
the question is whether some strategy profile is a Nash equilibrium for players who also insist that no resource ever goes
negative, and whose play keeps the resources nonnegative and meets a global specification.

**Games.** A *multi-player arena* $G = (S, (S_1 \uplus \cdots \uplus S_n), s_0, \{1, \dots, n\}, E, AP, \lambda)$ has a finite set $S$ of states
partitioned among $n$ players, an initial state $s_0$, an edge relation $E \subseteq S \times S$ and a labeling $\lambda : S \to 2^{AP}$ by
atomic propositions. Plays are infinite paths from $s_0$, histories are their finite prefixes, and a strategy of player $i$ maps each
history ending in $S_i$ to a successor of its last state. A profile $\sigma = (\sigma_1, \dots, \sigma_n)$ determines one outcome play
$\langle \sigma \rangle$. An objective is a set of plays, and player $i$ gets payoff $1$ if the outcome lies in their objective
$\Omega_i$ and $0$ otherwise.

**Resources.** A cost function $c : E \to \mathbb{Z}^k$, encoded in binary, describes the effect of each edge on $k$ common resources,
all starting at $0$. The *multi-energy objective* $\mathrm{En}(G)$ is the set of plays along which every prefix has total cost in
$\mathbb{N}^k$, so that no resource ever drops below $0$.

**Problem.** Given $G$, $c$, objectives $\Omega_1, \dots, \Omega_n$ and a global specification $\Omega$, a profile $\sigma$ is a solution of
*careful cooperative rational synthesis* if

$$
\langle \sigma \rangle \in \mathrm{En}(G) \cap \Omega
$$

and, for every player $i$ and every strategy $\sigma'_i$ of player $i$, if the outcome of $(\sigma_{-i}, \sigma'_i)$ lies in
$\Omega_i \cap \mathrm{En}(G)$, then $\langle \sigma \rangle \in \Omega_i$. A deviation thus counts only if it also keeps the resources
nonnegative. The problem asks whether a solution exists. Objectives are given in [linear temporal logic](../../../Logic/temporal-logic/linear-temporal-logic/formula.md); *reachability objectives*
have the form $\Diamond p$ for an atomic proposition $p$.

## Depends on

- [Arenas, strategies and memory structures](../muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)
- [Formulas of linear temporal logic](../../../Logic/temporal-logic/linear-temporal-logic/formula.md)

## Proof depends on

None.

## Sources

- R. Condurache, C. Dima, M. Jitaru, Y. Oualhadj and N. Troquard, "Careful autonomous agents in environments with multiple common resources", in *Proceedings of the 13th International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2022)*, Electronic Proceedings in Theoretical Computer Science 362, pp. 3–14, 2022, doi:10.4204/EPTCS.362.3; read in arXiv:2207.09707v1: Section 2 (multi-player arenas, plays and strategies, objectives and payoffs, LTL and multi-energy objectives, Nash equilibria, and the definition of careful cooperative rational synthesis).
