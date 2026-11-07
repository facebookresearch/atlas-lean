# Labels of the Hamiltonian path verifier

The instruction labels of the verifier: reading
$s$, $t$, $n$; validating the edge list and putting it back; validating the witness and putting
it back; the vertex loop, reading a vertex, and the head-or-edge dispatch; for each of the four
counter comparisons, the comparison itself and, for each of its three outcomes, the two loops
restoring the compared counters; the edge scan (comparing an edge's ends, with a flag for the
verdict so far, restoring the counters, putting the edge list back); the repeat scan (likewise
flagged comparisons and restores, then putting the witness back); the final nonzero-count
check; counting the vertex and making it the previous one; accept; and reject.
