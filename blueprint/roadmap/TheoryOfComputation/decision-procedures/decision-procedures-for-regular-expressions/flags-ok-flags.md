# Correctness of the flag pass

For a list $l$ of nodes and a natural number $k$, let $f_k$
be the entry at position $k$ of the flags of $l$, or the zero flags
$(\mathrm{false}, \mathrm{false}, \mathrm{false})$ if $k$ is at least the length of $l$. Then
$f_k$ describes the language of the regular expression at node $k$ of the encoding $l$ when $k$
is less than the length of $l$, and describes the empty language otherwise.
