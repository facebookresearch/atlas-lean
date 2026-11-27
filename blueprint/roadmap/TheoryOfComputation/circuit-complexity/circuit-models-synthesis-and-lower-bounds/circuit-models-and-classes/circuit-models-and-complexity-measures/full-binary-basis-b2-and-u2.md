# The full binary basis B2 and the basis U2

The *full binary Boolean basis* $B_2$ consists of all $16$ Boolean functions $\{0,1\}^2\to\{0,1\}$ (together with constants and projections). A $B_2$ gate is *genuinely binary* if it depends on both arguments; the ten such operations split into the eight *AND-type* operations $(x\oplus a)\wedge(y\oplus b)\oplus c$ with $a,b,c\in\{0,1\}$ and the two *XOR-type* operations $x\oplus y$ and $x\oplus y\oplus 1$. The basis $U_2$ is $B_2$ with the XOR-type operations removed: its binary gates are exactly the polarized conjunctions. The De Morgan basis $\{\wedge,\vee,\neg\}$ is, up to free negations, a basis of type $U_2$.

## Depends on

- [Straight-line programs and circuits over a basis](straight-line-program-over-a-basis.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Magnus Gausdal Find, Alexander Golovnev, Edward A. Hirsch, Alexander S. Kulikov, "A Better-than-3n Lower Bound for the Circuit Complexity of an Explicit Function", IEEE 57th Annual Symposium on Foundations of Computer Science, 89–98, 2016.
