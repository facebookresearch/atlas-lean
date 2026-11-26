# List membership with entry counting

For a type with decidable equality and an element $t$, the costed membership test of a list returns a Boolean and a count, by recursion: the empty list gives false with count $0$; a list starting with $x$ gives true with count $1$ if $t = x$, and otherwise the result for the rest of the list with $1$ added to its count. So the count is the position of the first occurrence of $t$, counted from $1$, or the length of the list when $t$ is absent.
