# Space-bounded single-tape machines

Let $s : \mathbb{N} \to \mathbb{N}$. A single-tape
Turing machine $M$ runs in space $s$ when, for every input word $l$ of length $|l|$, every
configuration reachable from the initial configuration of $M$ on $l$ uses at most $s(|l|)$
cells, whether or not the run halts. The cells used by a configuration are the head cell
together with the cells on each side of it up to the outermost non-blank cell.
