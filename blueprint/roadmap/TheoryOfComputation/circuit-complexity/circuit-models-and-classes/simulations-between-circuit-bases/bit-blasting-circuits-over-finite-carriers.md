# Bit-blasting circuits over a finite carrier with an injective encoding

Let $F$ be a set with an injective encoding $\mathrm{enc}:F\to\{0,1\}^w$ and a decoder $\mathrm{dec}$ with $\mathrm{dec}\circ\mathrm{enc}=\mathrm{id}_F$. There is a constant $\beta(w)$, depending only on $w$, such that every circuit over a basis of operations on $F$ of arity at most two with $s$ gates, $N$ inputs and $M$ outputs is simulated by a Boolean circuit on $Nw$ inputs and $Mw$ outputs with at most $s\cdot\beta(w)$ gates: on every encoded input it outputs the encodings of the outputs. In particular, for every finite nonempty $F$ one may take $w=\lceil\log_2|F|\rceil$, so circuits over any finite carrier (for instance arithmetic circuits over a finite field) are simulated by Boolean circuits with constant-factor overhead.

## Proof sketch

Each operation of arity at most two is a function $\{0,1\}^{2w}\to\{0,1\}^w$ on encodings (arbitrary off the image), which has a fixed Boolean circuit of size at most $\beta(w)$; substitute these gadgets gate by gate.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
