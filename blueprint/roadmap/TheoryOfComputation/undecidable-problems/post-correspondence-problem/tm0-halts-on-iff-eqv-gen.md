# A single-tape machine halts iff its start word is Thue equivalent to the halting word

Let
$M$ be a single-tape Turing machine with finitely many states and tape symbols, write $\vdash$ and
$\dashv$ for the left and right end markers and $H$ for the halting symbol, and let $l$ be an input
word of tape symbols. Then $M$ halts on $l$ if and only if the start word of $l$ and the halting
word ${\vdash}\,H\,{\dashv}$ are equivalent under the reflexive, symmetric and transitive closure
of one-step rewriting by the rewriting system simulating $M$.
