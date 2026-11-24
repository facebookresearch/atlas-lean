# Labels of the CLIQUE verifier

On an instance with target size $k$ and $n$ vertices, the
verifier machine has the labels: read $k$, read $n$, load the witness, walk a row (carrying a bit
$c$, the conjunction of the row's pair conditions so far), put the row back, accept, and
reject.
