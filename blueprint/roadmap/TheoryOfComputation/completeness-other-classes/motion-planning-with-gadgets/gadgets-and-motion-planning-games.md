# Gadgets and motion-planning games

A gadget is a finite-state device with locations that a robot can traverse between, each traversal changing its state; a
system of gadgets joined by a connection graph is the board of one-player, two-player and team motion-planning games.

**Gadgets.** A *gadget* has a finite set of *locations* and a finite set of *states*. Its *transition graph* has a vertex
for each pair (state, location) and an edge from $(s, a)$ to $(s', b)$ when a robot may enter at location $a$ in state $s$,
exit at location $b$, and leave the gadget in state $s'$. A *$k$-tunnel* gadget has $2k$ locations paired by a perfect
matching into *tunnels*, and each state only says in which direction(s) each tunnel can be traversed. A gadget is
*deterministic* if its transition graph has out-degree at most $1$, and *reversible* if the reverse of every edge of its
transition graph is again an edge. A gadget has *interacting tunnels* if traversing some tunnel changes the traversability
of another tunnel of the same gadget. The *locking 2-toggle* is the $2$-tunnel gadget with three states: in one state either tunnel
can be traversed in one direction, and such a traversal blocks the other tunnel until it is reversed.

**Systems and games.** A *system of gadgets* consists of gadgets, their initial states and a *connection graph* on their
locations; a robot moves freely along the connection graph and changes position otherwise only by traversing a gadget
according to its current state, each traversal counting as one move. In the *one-player game* one asks whether a robot can
reach a goal location from its start location. In the *two-player game* two players alternately move their own robots, with
complete information, and one asks whether the first player has a forced win, reaching its goal before the opponent does. In
a *team game* there are more than two robots, each moved by its own player, and the players are partitioned into two teams,
White and Black. The players move one at a time, in a fixed cyclic order of all players given with the instance, and a team
wins when one of its robots reaches its goal. After the start each player sees only the states of the gadgets its robot can
reach through the connection graph, and one asks whether the White team has a forced win.

Gadgets are local: a traversal changes only the state of the traversed gadget. Deterministic reversible gadgets are those
whose transition graph is the bidirectional version of a matching. With unboundedly many moves, one-player games with any
interacting-tunnel reversible deterministic $k$-tunnel gadget are PSPACE-complete and two-player games EXPTIME-complete,
while gadgets without interacting tunnels make the one-player game solvable in NL.

## Depends on

None.

## Proof depends on

None.

## Sources

- E. D. Demaine, D. H. Hendrickson, J. Lynch, "Toward a general complexity theory of motion planning: characterizing which gadgets make games hard", in *11th Innovations in Theoretical Computer Science Conference (ITCS 2020)*, Leibniz International Proceedings in Informatics 151, Schloss Dagstuhl, 2020, article 62, doi:[10.4230/LIPIcs.ITCS.2020.62](https://doi.org/10.4230/LIPIcs.ITCS.2020.62). Numbering of the version read, arXiv:1812.03592v2 (titled "Toward a General Theory of Motion Planning Complexity: Characterizing Which Gadgets Make Games Hard"): Sections 1.1 and 1.2 (the gadget model, systems of gadgets, the one-player, two-player and team games, $k$-tunnel, deterministic and reversible gadgets) and Section 1.3 (interacting tunnels and the locking 2-toggle).
