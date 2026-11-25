# Outputs are unique

If a single-tape Turing machine $M$ outputs the word $l_1$ on the
input $l$ and also outputs the word $l_2$ on the input $l$, then $l_1 = l_2$. Here $M$ outputs a
word $w$ on $l$ when its run from the initial configuration on $l$ halts with exactly $w$ on the
tape, every other cell blank and the head on the first symbol of $w$ (an all-blank tape if $w$ is
empty).

The run of a machine is determined by its input, and a halting configuration has no successor.
