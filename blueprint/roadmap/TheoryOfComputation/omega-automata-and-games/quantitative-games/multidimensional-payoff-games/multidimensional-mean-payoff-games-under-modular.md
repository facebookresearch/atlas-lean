# Multidimensional mean-payoff recursive games under modular strategies are undecidable

No algorithm decides whether the first player of a recursive (pushdown) game with multidimensional mean-payoff objectives has a modular winning strategy, already for six dimensions, three modules, no recursion and single exits.

A *weighted recursive game graph* is a tuple of game modules $A_0,A_1,\dots,A_n$; each module has nodes with entry and exit nodes, *boxes* that call other modules, a partition of nodes and boxes between player 1 and player 2, and a transition relation from nodes and returns of boxes to nodes and calls of boxes, with weights in $\mathbb Z^k$ on transitions; $A_0$ is the initial module. The configurations (a stack of boxes and a node) form the global game graph, which is isomorphic to a pushdown game graph computable in polynomial time. A *modular strategy* for player 1 is a family of local strategies $\tau_i$, one per module, where the next move depends only on the *local history*, the sequence of nodes visited in the current invocation of the module, and not on the calling context; player 2 plays general strategies. Player 1 wins if the mean payoff of the play is $\ge\vec0$ in every dimension (see [classical quantitative objectives](../classical-quantitative-objectives.md)).

**Theorem.** Deciding whether player 1 has a modular winning strategy in a weighted recursive game graph with multidimensional mean-payoff objectives is undecidable, even for hierarchical games (no recursive calls) with six dimensions, three modules, and at most one exit per module (Theorem 4 of the source).

For one-dimensional mean-payoff objectives the modular winning strategy problem is NP-hard (and NP-complete by Chatterjee and Velner's earlier work), and the source gives an algorithm that runs in polynomial time when the number of modules, the number of exits and the maximal absolute weight are bounded.

## Depends on

- [Classical quantitative objectives](../classical-quantitative-objectives.md)
- [Modular games on recursive game graphs](../../infinite-state-games/modular-games-on-recursive-game-graphs/modular-games-on-recursive-game-graphs.md)
- [Arenas, strategies and memory structures](../../muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction is from reachability games over $\mathbb Z^2$ (Lemma 16 of the source), where player 1 wins if the accumulated weight vector plus an initial vector $\vec\nu$ becomes $\vec0$ at a player-1 vertex; their undecidability extends the proof for reachability games over $\mathbb N^2$ (Abdulla, Bouajjani and d'Orso). From a game over $\mathbb Z^k$ the source builds three modules with $2k+2$ dimensions: $A_0$ calls $A_1$ and $A_2$ forever; $A_1$ loops on weight $(0,\dots,0,+1,-1)$; $A_2$ adds $(\vec\nu,-\vec\nu,0,0)$, plays the reachability game with each edge $e$ weighted $(w(e),-w(e),-1,+1)$, lets player 1 move from any of his vertices to a vertex $v^*$ that loops on $(0,\dots,0,-1,+1)$, and then exits. Player 1 must exit $A_1$ and must reach $v^*$ on every play, or some dimension has mean payoff $-1$; the first $2k$ dimensions force the accumulated vector to be exactly $\vec0$ when $v^*$ is entered, and because a modular strategy cannot depend on earlier invocations, a modular winning strategy exists iff player 1 wins the reachability game. For $k=2$ this gives six dimensions.

## Sources

- Krishnendu Chatterjee and Yaron Velner, "Hyperplane separation technique for multidimensional mean-payoff games", *Journal of Computer and System Sciences* 88, 2017, pp. 236–259, doi:[10.1016/j.jcss.2017.04.005](https://doi.org/10.1016/j.jcss.2017.04.005); conference version in *CONCUR 2013*, Lecture Notes in Computer Science 8052, pp. 500–515, doi:[10.1007/978-3-642-40184-8_35](https://doi.org/10.1007/978-3-642-40184-8_35); read in arXiv:1210.3141v2 ([arXiv](https://arxiv.org/abs/1210.3141v2)): the section on recursive games under modular strategies, with the definitions of weighted recursive game graphs and modular strategies, the subsection on undecidability for multidimensional objectives (the lemma on reachability games over $\mathbb Z^2$ and the undecidability theorem), and the subsections on NP-hardness and the one-dimensional algorithm.
