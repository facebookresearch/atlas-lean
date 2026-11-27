# Linear-size population counting and threshold circuits

There is a constant $c$ such that for every $n$ the binary representation of the Hamming weight $|x|=\sum_i x_i$ of $x\in\{0,1\}^n$ is computed by a De Morgan circuit with at most $cn$ gates (all gates charged). Consequently every threshold function $\mathrm{Th}^n_{\ge t}$, and every symmetric function of $n$ bits, has De Morgan circuits of size $O(n)$.

## Proof sketch

Pad to a power of two and add along a balanced binary tree using ripple-carry adders; a node at height $h$ adds $(h+1)$-bit words, and there are $n/2^{h}$ such nodes, so the total cost $\sum_h O(h)\,n/2^h$ is $O(n)$. A comparison with the constant $t$ adds $O(\log n)$ gates.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)
- [Ripple-carry adder](../../../ripple-carry-adder/ripple-carry-adder.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987.
