# Usefulness of a property against constant-depth circuit classes

Let $\mathcal{C}=(\mathcal{C}_n)$ be a property of Boolean functions and let $\mathsf{ConstDepth}[\Omega]$ be the class of languages with polynomial-size constant-depth circuits over a basis $\Omega$. $\mathcal{C}$ is *useful against* $\mathsf{ConstDepth}[\Omega]$ if for every depth bound $d$ and every polynomial size bound $s(n)$, for all sufficiently large $n$, every function in $\mathcal{C}_n$ (and $\mathcal{C}_n$ is nonempty) requires circuits over $\Omega$ of depth $d$ to have more than $s(n)$ gates. A language whose slices lie in a useful property is outside the class.

## Depends on

- [Natural property](../../../hierarchy-theorems-and-barriers/natural-proofs-barrier/natural-property.md)
- [The AC, TC and AC[q] hierarchies](../../parallel-circuit-hierarchies/ac-tc-and-acq-hierarchies.md)

## Sources

- Alexander A. Razborov, Steven Rudich, "Natural Proofs", Journal of Computer and System Sciences 55(1), 1997.
