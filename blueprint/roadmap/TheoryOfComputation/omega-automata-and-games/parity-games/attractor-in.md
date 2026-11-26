# Attractor inside a set of positions

Let $G$ be an encoded parity game on $n$ positions,
$p$ a player (encoded as a Boolean: false for even, true for odd), and $T$, $U$ sets of
positions. The attractor of $T$ for $p$ inside $U$ is the set obtained from $\emptyset$ by
applying $n$ times the map $X \mapsto (T \cap U) \cup \mathrm{CPre}_p^U(X)$, where
$\mathrm{CPre}_p^U(X)$ is the controllable predecessor of $X$ for $p$ inside $U$.
