# Controllable predecessor inside a set of positions

Let $G$ be an encoded parity game,
$p$ a player (encoded as a Boolean: false for even, true for odd), and $U$, $X$ sets of
positions. The controllable predecessor of $X$ for $p$ inside $U$ is the set of positions
$v \in U$ such that either $v$ is owned by $p$ and some move of $G$ goes from $v$ to a position
of $U \cap X$, or $v$ is not owned by $p$ and every move of $G$ from $v$ to a position of $U$
ends in $X$.

Moves leaving $U$ are ignored; in particular a position of $U$ not owned by $p$ with no move into
$U$ belongs to the set.
