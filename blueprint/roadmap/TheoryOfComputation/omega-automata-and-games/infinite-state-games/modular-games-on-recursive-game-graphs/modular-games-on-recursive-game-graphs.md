# Modular games on recursive game graphs

A recursive game graph is a two-player game graph made of modules that call each other like procedures; a modular strategy decides
moves inside a module activation using only the history of that activation, and the modular game problem asks whether player 0 has
a modular strategy all of whose plays satisfy a given winning condition.

**Recursive game graphs.** A *recursive game graph* $G = (M, m_{in}, \{S_m\}_{m \in M})$ over a set $AP$ of atomic propositions has a finite set
$M$ of modules, a main module $m_{in}$ that no module calls, and for each module a *game module* $S_m$ consisting of nodes $N_m$ with a unique
entry $e_m$ and a set $\mathit{Ex}_m$ of exits, boxes $B_m$ with a map $Y_m : B_m \to M \setminus \{m_{in}\}$ to the modules they call, a transition
function from nodes and returns to nodes and calls, where a *call* is a pair $(b, e_{Y_m(b)})$ and a *return* a pair $(b, x)$ with
$x \in \mathit{Ex}_{Y_m(b)}$, a labeling $\eta_m$ of nodes, calls and returns by subsets of $AP$, and a partition of the non-exit nodes and the
returns into positions of player 0 and of player 1. Entries have no incoming and exits no outgoing transitions.

**Plays.** A state is a pair of a call stack of boxes and a vertex. A play starts at $(\varepsilon, e_{m_{in}})$ and proceeds by internal moves
along transitions, chosen by the owner of the current position; by *calls*, which push the box and move to the entry of the called module;
and by *returns*, which pop the box at an exit $x$ and move to the return $(b, x)$. The word of a play is the sequence of labels of its
vertices, an infinite word over $\Sigma = 2^{AP}$.

**Modular strategies.** The *local memory* at a position of a play is the sequence of vertices of the current module activation, from its
entry, skipping each completed call to its matching return. A *modular strategy* of player $\ell$ is a family $\{f_m\}_{m \in M}$ of functions
mapping each local history in $S_m$ ending in a position of player $\ell$ to a successor; a play conforms to it if player $\ell$'s moves follow
$f_m$ applied to the local memory. Each new activation of a module starts with fresh memory.

**Modular games.** A *modular game* $\langle G, L \rangle$ adds a winning condition $L \subseteq \Sigma^\omega$. A modular strategy of player 0 is winning if
the word of every play conforming to it lies in $L$, and the *modular game problem* asks whether player 0 has a winning modular strategy. In a
*pushdown modular game* $L$ is the language of a pushdown automaton $P = (Q, q_0, \Sigma, \Gamma, \delta, \gamma_\bot, F)$ over $\Sigma$, with finite sets of states and stack symbols, $\varepsilon$-moves allowed and a set $F \subseteq Q$ defining its acceptance condition; its stack is not synchronized with the calls and returns
of $G$. In the *deterministic* version each $\delta(q, \alpha, \gamma)$ has at most one element, and no state and stack symbol with an $\varepsilon$-move has a move on a letter.

## Depends on

- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Sources

- I. De Crescenzo, S. La Torre and Y. Velner, "Visibly pushdown modular games", in *GandALF 2014*, Electronic Proceedings in Theoretical Computer Science 161, pp. 260–274, 2014, doi:10.4204/EPTCS.161.22; journal version *Information and Computation* 253:204–223, 2017, doi:10.1016/j.ic.2016.07.007. Read in arXiv:1408.5969v1: Section 2, Definition 1 (recursive game graphs), plays, modular strategies, winning conditions and modular games, and Section 3 (pushdown modular games).
