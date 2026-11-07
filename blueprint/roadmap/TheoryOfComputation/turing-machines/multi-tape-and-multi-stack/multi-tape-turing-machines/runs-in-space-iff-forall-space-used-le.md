# Space bounds of deterministic machines

Let $M$ be a deterministic multi-tape Turing
machine, $x$ an input and $s \in \mathbb{N}$. Then $M$ runs in space $s$ on $x$, that is, every
computation path of $M$ on $x$ visits at most $s$ work-tape cells, if and only if for every
$t \in \mathbb{N}$ the run of $M$ from the initial configuration on $x$ visits at most $s$
work-tape cells within its first $t$ steps. Visited cells are counted on each work tape
separately and summed over the work tapes.
