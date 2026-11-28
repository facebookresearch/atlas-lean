# The single-tape machine outputs the answer in time

If a machine code $c$ decides a problem $L$ on bit strings within time $t$, and every cell to the left of the head of $c$ is blank after $t(|x|)$ steps on a bit string $x$, then the single-tape machine of $c$, on the input word of $x$, halts within $t(|x|) + 1$ steps with output the one-symbol word consisting of the input symbol of $L(x)$.
