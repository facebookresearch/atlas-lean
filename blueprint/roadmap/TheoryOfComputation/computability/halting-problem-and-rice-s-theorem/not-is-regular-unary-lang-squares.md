# The unary squares are not regular

The unary language of the perfect squares, the set of
words over a one-letter alphabet whose length is $m^2$ for some $m \in \mathbb{N}$, is not regular.

The proof uses the pumping lemma: if a DFA with $N$ states accepted this language, pumping the word
of length $N^2$ by a block of length between $1$ and $N$ would give a length strictly between $N^2$
and $(N + 1)^2$.
