# Run of the load phase of the 3-COLOR verifier

Let $n$ be a natural number and $w$, $a$
lists of bits. Start the verifier at its load label, in any internal state, with stacks in which
the counter $N$ holds exactly $n$ units, the witness stack $W$ holds $w$ and the scratch stack $T$
holds $a$. Then within at most $n + 1$ steps the verifier reaches the label that moves the codes
onto the color stack $P$ if $w$ has at least $2n$ bits and the color codes of the vertices
$0, \dots, n - 1$ (vertex $i$ has the code $w_{2i} w_{2i+1}$) are all valid, that is, none is
$11$; otherwise it reaches the rejecting label. In the first case $T$ then holds the first $2n$
bits of $w$ in reverse order on top of $a$, and every stack other than $N$, $W$ and $T$ is as at
the start.
