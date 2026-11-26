# Lower bound for black pebbling from disjoint ancestor sets

The **ancestors** of a vertex $u$ are $u$ itself and every vertex from which $u$ is reachable. Say that $v$ **forces $k$ pebbles** if every pebbling of $v$ reaches a configuration with at least $k$ pebbles, that is, $\mathrm{Peb}(G,v)\ge k$. If $v$ has exactly two predecessors $u_1,u_2$, each forcing $k$ pebbles, and no vertex is an ancestor of both, then $v$ forces $k+1$ pebbles.

## Proof sketch

In a pebbling of $v$, let $s_i$ be the last moment before $v$ is pebbled at which no ancestor of $u_i$ ($u_i$ included) carries a pebble, and say $s_1\le s_2$. After $s_2$, the moves on the ancestors of $u_2$ pebble $u_2$ from nothing (every predecessor of an ancestor is an ancestor, so these moves are legal on their own), so at some moment they carry $k$ pebbles, while the ancestors of $u_1$ still carry one. The two ancestor sets are disjoint, so that moment has $k+1$ pebbles.

## Depends on

- [Black pebble game and black pebbling price](black-pebble-game.md)

## Sources

- Jakob Nordström, "New Wine into Old Wineskins: A Survey of Some Pebbling Classics with Supplemental Results", manuscript, version of 19 November 2010, https://people.csail.mit.edu/jakobn/research/PebblingSurveyTMP.pdf (the induction over the height behind Theorem 4.1, for complete binary trees).
