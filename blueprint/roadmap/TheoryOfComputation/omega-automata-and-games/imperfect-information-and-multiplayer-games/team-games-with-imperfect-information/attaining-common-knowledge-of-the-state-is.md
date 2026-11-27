# Attaining common knowledge of the state within a region of a game graph is undecidable

For finite game graphs in which several players with private observations move against Nature, no algorithm decides whether some nontrivial history staying inside a given set of states reaches a point where the current state is common knowledge among the players.

**Game graphs.** There are players $1, \dots, n$ and an agent Nature. Each player $i$ has a finite set $A^i$ of actions and a finite set $B^i$ of observations. A *game graph* $G = (V, E, (\beta^i)_i)$ has a finite set $V$ of states, an initial state $v_0$ known to all players, moves $E \subseteq V \times A \times V$ labeled by action profiles (every state has a move for every profile) and observation functions $\beta^i \colon V \to B^i$. In each round every player chooses an action, Nature chooses a successor along a move with that action profile, and every player $i$ receives the observation $\beta^i$ of the new state. A *history* is a finite sequence $v_0 a_1 v_1 \cdots a_\ell v_\ell$ of states and action profiles following the moves. Player $i$ cannot distinguish histories $\pi \sim^i \pi'$ with the same sequence of own actions and observations $\beta^i(v_0)\, a^i_1\, \beta^i(v_1) \cdots$.

**Common knowledge of the state.** For a set $F$ of histories, player $i$ knows $F$ at $\pi$ if every $\pi' \sim^i \pi$ lies in $F$, and $F$ is common knowledge at $\pi$ if $\pi$ belongs to every iterate $K^{i_1}(K^{i_2}(\cdots K^{i_k}(F)))$ of these knowledge operators. The players *attain common knowledge of the state* at $\pi$ if the set of histories that end at the same state as $\pi$ is common knowledge at $\pi$. A history is *within* $S \subseteq V$ if all its states lie in $S$.

**Theorem (Berwanger and Mathew).** It is undecidable whether, for a given game graph and a designated subset $S$ of states, there is a nontrivial history within $S$ at which the players attain common knowledge of the state.

Whether the players attain common knowledge of the state at a given history is PSPACE-complete, and whether a game allows recurring common knowledge of the state (common knowledge of the state infinitely often along every play) is decidable, as the same paper shows.

## Depends on

None.

## Proof depends on

None.

## Expansion

The proof reduces the corridor universality problem for domino systems, undecidable by results of van Emde Boas and of Latteux and Simplot, which has no page here: from a domino system with a designated set of dominoes one builds a game graph and a set $S$ of states such that the players attain common knowledge of the state at some nontrivial history within $S$ if and only if some frontier constraint admits no corridor tiling, the observations along the history spelling such a constraint.

## Sources

- D. Berwanger and A. B. Mathew, "Infinite games with finite knowledge gaps", *Information and Computation* 254 (2017), pp. 217–237, doi:10.1016/j.ic.2016.10.009; read as arXiv:1411.5820v2, <https://arxiv.org/abs/1411.5820v2>: Proposition 4.3 (the undecidability statement) with its proof, Theorem 2.2 (complexity of corridor tiling problems, cited there), the definitions of game graphs, histories, indistinguishability and common knowledge in Section 2, and Section 4 (common knowledge of the state), in the numbering of that version.
