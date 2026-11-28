# Deciding codes on single-tape machines

If a machine code $c$ decides a problem $L$ on bit strings within time $t$, then on the input word of every bit string $x$ the single-tape machine of $c$ halts within $t(|x|) + 1$ steps, with the answer symbol of $c$ for $L(x)$ under the head and every cell to the right of the head blank. The cells to the left of the head read as the cells to the left of the head of $c$ after $t(|x|)$ steps.
