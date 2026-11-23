# The CLIQUE, INDEPENDENT-SET and VERTEX-COVER verifier as a host component

For a [mode](../part-02/mode.md) $m$ (clique, independent set or vertex cover), the component
machine whose stack indices, stack alphabets, labels and program are those of the
[verifier machine](../part-04/prog.md) of mode $m$: its six stacks $X, W, C, N, V, T$ each hold
symbols of the SAT verifier's alphabet, and they are listed exactly once, in that order.
