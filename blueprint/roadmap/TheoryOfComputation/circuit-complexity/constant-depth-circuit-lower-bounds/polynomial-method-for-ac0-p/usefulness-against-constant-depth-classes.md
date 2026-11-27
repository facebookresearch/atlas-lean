# Usefulness of a property against constant-depth circuit classes

Let $\mathcal{C}=(\mathcal{C}_n)$ be a property of Boolean functions, $\mathcal{C}_n$ a set of functions $\{0,1\}^n\to\{0,1\}$, and let $\mathsf{ConstDepth}[\Omega]$ be the class of languages (equivalently, sequences of Boolean functions $f_n$ on $n$ bits) with polynomial-size constant-depth circuits over a basis $\Omega$. $\mathcal{C}$ is *useful against* $\mathsf{ConstDepth}[\Omega]$ if for every sequence of functions $(f_n)$ such that $f_n\in\mathcal{C}_n$ for infinitely many $n$, the sequence $(f_n)$ is not in $\mathsf{ConstDepth}[\Omega]$. In particular a language whose slices lie in a useful property is outside the class.

## Depends on

- [Natural property](../../../hierarchy-theorems-and-barriers/natural-proofs-barrier/natural-property.md)
- [The AC, TC and AC[q] hierarchies](../../parallel-circuit-hierarchies/ac-tc-and-acq-hierarchies.md)

## Sources

- Alexander A. Razborov, Steven Rudich, "Natural Proofs", Journal of Computer and System Sciences 55(1), 24–35, 1997 (Section 2.2, the usefulness condition).
