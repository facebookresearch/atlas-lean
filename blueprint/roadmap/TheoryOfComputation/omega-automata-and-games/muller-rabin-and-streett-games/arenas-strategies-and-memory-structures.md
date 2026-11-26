# Arenas, strategies and memory structures

A *graph* has a set $V$ of vertices and a set $E$ of edges, each from a vertex to a vertex, and every vertex has at least
one outgoing edge. An *arena* is a graph together with a partition $V = V_{\mathrm{Eve}} \uplus V_{\mathrm{Adam}}$ of its vertices
between the two players, Eve and Adam. A *play* is a path in the graph: from the current vertex, its owner chooses an
outgoing edge. A *strategy* for Eve is a map $\sigma$ from finite plays ending in $V_{\mathrm{Eve}}$ to outgoing edges of their last
vertex; a play is *consistent* with $\sigma$ if every move made at a vertex of Eve is the one $\sigma$ prescribes. Strategies for
Adam are defined symmetrically.

A *qualitative game* is an arena with a *condition* $W$, a set of infinite plays won by Eve; the others are won by Adam.
A strategy is *winning from* $v$ if every infinite play from $v$ consistent with it is won by its player, and the *winning
region* of a player is the set of vertices from which that player has a winning strategy. The game is *determined* if every
vertex lies in the winning region of one of the players.

A *memory structure* is a triple $\mathcal{M} = (M, m_0, \delta)$ of a set $M$ of memory states, an initial state $m_0$ and an update
function $\delta : M \times E \to M$, extended to finite sequences of edges; its *size* is $|M|$. A strategy *using* $\mathcal{M}$ is a map
$\hat\sigma : V_{\mathrm{Eve}} \times M \to E$, inducing the strategy that plays $\hat\sigma(\mathrm{last}(\pi), \delta^*(\pi))$ after the finite play $\pi$.
A strategy has *finite memory* if it uses a finite memory structure, and it is *positional* if it uses a memory structure
with one state, that is, it depends only on the current vertex. A condition is *positional* (for Eve) if, in every game with
that condition, Eve has a positional winning strategy from every vertex from which she has a winning strategy; it is
*positionally determined* if moreover every game with that condition is determined, and *bi-positionally determined* if both
players have positional winning strategies from their winning regions. It is *determined with memory* $m$ if in every game
with that condition, from every vertex, either Eve has a winning strategy using a memory structure of size at most $m$ or Adam
has a winning strategy.

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 1 (N. Fijalkow, "Introduction"): Definitions 1.1 and 1.2 (graphs and arenas), the paragraphs on playing and strategies, Definitions 1.3–1.7 (conditions, games, winning regions, determinacy and positionality), and Section 1.8 (memory structures and finite-memory determinacy).
