# Overwriting a function on a finite set of indices

Let $\iota$ be a type with decidable equality, $(\pi_i)_{i \in \iota}$ a family of types,
$x \in \prod_{i \in \iota} \pi_i$, $s$ a finite subset of $\iota$ and
$y \in \prod_{i \in s} \pi_i$. The function obtained by overwriting $x$ with $y$ on $s$ is the
$z \in \prod_{i \in \iota} \pi_i$ with $z_i = y_i$ for $i \in s$ and $z_i = x_i$ for
$i \notin s$.
