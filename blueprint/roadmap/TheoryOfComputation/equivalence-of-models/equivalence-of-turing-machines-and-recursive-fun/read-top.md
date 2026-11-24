# Reading the top of a coded stack

Let $k$ be a stack index of the machine and let $S$ assign
to each stack index $j$ a list $S_j$ of natural numbers (codes of symbols). The top of stack $k$ as
read from $S$ is no symbol when $S_k$ is empty. Otherwise, if $c$ is the first entry of $S_k$, it is
the decoding of $c$: the symbol of $\Gamma_k$ at position $c$, counting from $0$, in the list of
relevant symbols of stack $k$, or no symbol when $c$ is at least the length of that list.
