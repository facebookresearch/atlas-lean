# Step bound of one simulated step

For a code $c$ and a configuration $k$ with state $q$,
head cell $h$, nearest left cell $l$ and nearest right cell $r$ (each read as the blank $0$ when
there is no such cell), let $|C|$ be the length of the code stack of $c$. The step bound of $c$
at $k$ is $10|C| + q + h + l + r + 10$.
