# Winning positions in Geography

Let $E$ be a list of pairs of natural numbers, read as
directed edges, let $v$ be a natural number (the current vertex) and let $V$ be a list of natural
numbers (the visited vertices). For a natural number $k$ (the fuel), the predicate
$\mathrm{GeoWins}(k, E, v, V)$ is defined by recursion on $k$: $\mathrm{GeoWins}(0, E, v, V)$ is
false, and $\mathrm{GeoWins}(k + 1, E, v, V)$ holds exactly when there is a natural number $w$
with $(v, w) \in E$ and $w \notin V$ such that $\mathrm{GeoWins}(k, E, w, V')$ is false, where
$V'$ is the list $V$ with $w$ added at the front.

Read as a game, the player to move wins when they can move the token along an edge of $E$ to a
vertex not in $V$ from which the opponent does not win; a player with no such move, or with no
fuel left, loses.
