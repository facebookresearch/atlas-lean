# Forced wins in team multiplayer video games are undecidable

Whether a team has a forced win is undecidable in a graph game with two teams, timed movement, visibility and guarded edges, and hence in generalized team versions of Team Fortress 2, Super Smash Bros. and Mario Kart in which team members cannot communicate.

**Team graph game.** An instance consists of a directed graph $G=(V,E)$ with edge weights in $\mathbb N$ (traversal times), start nodes $s_r,s_b$ for a red and a blue team and a win node $w$, a directed visibility relation $S\subseteq V^2$, an attack relation $A\subseteq V^2$, and numbers $n_r,n_b$ of players. The game starts with $n_r$ red tokens at $s_r$ and $n_b$ blue tokens at $s_b$ and proceeds in frames: in each frame all active players simultaneously choose a neighboring node to move towards, or to stay, and then every player learns the position and team of each token it can see. A player crossing an edge guarded by an enemy at an attacking node is eliminated. A team wins if all enemy tokens are eliminated or one of its tokens reaches $w$. A team has a *forced win* if its members have strategies, each depending only on what that member has seen, that guarantee a win.

**Theorem (Coulombe and Lynch).** There is a computable map $h$ from instances $D$ of the [team DFA game](the-team-dfa-game-and-its-communication-variant.md) to instances of the team graph game such that the existential team has a forced win on $D$ if and only if the blue team has a forced win on $h(D)$ (Theorem 3); hence it is undecidable whether the blue team has a forced win in the team graph game (Corollary 4).

The same paper realizes the team graph game in video games, which are therefore undecidable as well: in a generalized Super Smash Bros. match between two teams of Pikachus on some stage, it is undecidable whether Player 1's team has a forced win (Theorem 5); in generalized Mario Kart Balloon Battle with the Bob-ombs Only item distribution, it is undecidable whether the blue team has a forced win (Theorem 6); and Team Fortress 2, in a king-of-the-hill match with unlimited time and default loadouts, simulates the team graph game directly (Section 4.1).

In all these games the map size and the number of players are unbounded, and team members cannot communicate except through their actions in the game: they are not co-located, see only their own screens, and all chat is disabled. The source also shows that the team DFA game and the team computation game of Hearn and Demaine reduce to each other (Lemma 7). The undecidability holds although each game instance has a bounded configuration space.

## Depends on

- [The team DFA game and its communication variant](the-team-dfa-game-and-its-communication-variant.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The team DFA game is undecidable](the-team-dfa-game-is-undecidable.md)

## Expansion

The source defines the team graph game informally (Definition 2), so a complete expansion first fixes its rules precisely: what each player observes in a frame through the visibility relation, how simultaneous moves along weighted edges are timed, exactly when the attack relation eliminates a token crossing a guarded edge, the order in which eliminations and arrivals at $w$ are resolved within a frame, and the strategies of each team member as functions of that member's own observation history.

The map $h$ builds the graph from gadgets. The state of the DFA is the position of one blue player, the runner, inside a state transition gadget; the other blue players, the executors, supply the blue team's input bits by choosing among unguarded paths in choice gadgets, and red players supply the red team's input by guarding some of those paths. Delay gadgets, in which a red guard blocks the runner until an executor arrives to threaten it, synchronize all players so that inputs and transitions occur in the right order, and an initializer gadget sends players from their start nodes to their places. An accepting state of the DFA leaves the runner a free path to $w$. Each video game then realizes the gadgets with its own mechanics: hallways, glass walls, Demoman grenades and Sniper rifles in Team Fortress 2, Pikachu's Thunder attack in Super Smash Bros., and Bob-ombs on a battle course in Mario Kart.

## Sources

- Michael J. Coulombe and Jayson Lynch, "Cooperating in video games? Impossible! Undecidability of team multiplayer games", in *9th International Conference on Fun with Algorithms (FUN 2018)*, Leibniz International Proceedings in Informatics 100, paper 14, pp. 14:1–14:16, 2018, doi:[10.4230/LIPIcs.FUN.2018.14](https://doi.org/10.4230/LIPIcs.FUN.2018.14); read in the open-access published version ([PDF](https://drops.dagstuhl.de/storage/00lipics/lipics-vol100-fun2018/LIPIcs.FUN.2018.14/LIPIcs.FUN.2018.14.pdf)): the gadgets of Section 2, Definition 2, Theorem 3 and Corollary 4 in Section 3, Section 4.1 and Theorems 5 and 6 in Section 4, and Lemma 7 and Corollary 8 in Appendix A.
- Michael J. Coulombe and Jayson Lynch, journal version under the same title, *Theoretical Computer Science* 839, pp. 30–40, 2020, doi:[10.1016/j.tcs.2020.05.028](https://doi.org/10.1016/j.tcs.2020.05.028) (cited, not read).
