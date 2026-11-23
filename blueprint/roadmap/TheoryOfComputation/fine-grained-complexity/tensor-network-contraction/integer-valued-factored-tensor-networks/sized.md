# Shaped tensor network with bounded entries

A factored tensor network on a finite linearly ordered vertex set has size parameters
$P, B \in \mathbb{N}$ when it has shape parameter $P$ and

- $|W_a(z)| \le 2^B$ for every vertex $a$ and state $z$;
- $|f_{a,b}(z, \theta)| \le 2^B$ for all vertices $a, b$, states $z$ and labels $\theta$;
- $|I_{a,b}(z, z')| \le 2^B$ for all distinct vertices $a, b$ and all states $z, z'$, where
  $I_{a,b}$ is the interaction.
