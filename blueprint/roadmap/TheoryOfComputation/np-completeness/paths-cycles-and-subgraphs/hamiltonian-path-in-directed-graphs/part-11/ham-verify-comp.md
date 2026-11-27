# The HAMPATH verifier as a host component

The component machine whose stack indices, stack alphabets, labels and program are those of the
[HAMPATH verifier machine](../part-10/prog.md): its twelve stacks (the input $X$, the witness $W$,
the counters $S, T, N, C, A, B$, the save stacks $E, Z$ and the scratch stacks $R, Q$) each hold
symbols of the SAT verifier's alphabet, and they are listed exactly once, in the order
$X, W, S, T, N, C, A, B, E, Z, R, Q$.
