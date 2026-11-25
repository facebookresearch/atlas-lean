# Cost of the Boolean certificate verifier

Let $c$ be a circuit over the Boolean signature
with $n$ inputs, $s$ gates and one output, and let $b$ be an array of $m$ truth values. The cost
counted by the Boolean certificate verifier on $b$ is $2 + s + \sum_{j < s} a_j$ if $m = n + s$,
where $a_j$ is the number of arguments of gate $j$, and $1$ otherwise.
