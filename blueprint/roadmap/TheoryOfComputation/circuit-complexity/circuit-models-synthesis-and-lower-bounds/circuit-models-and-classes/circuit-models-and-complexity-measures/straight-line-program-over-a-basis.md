# Straight-line programs and circuits over a basis

Let $U$ be a carrier set and let $\Omega$ be a *basis*: a set of operation symbols, each with an arity $k\ge 0$ and an interpretation $\omega^U : U^k\to U$. A *straight-line program* (or *circuit*) over $\Omega$ with $n$ inputs is a finite sequence of *gates* $g_1,\dots,g_s$, where each $g_j$ is an operation $\omega_j\in\Omega$ of arity $k_j$ together with $k_j$ argument wires chosen among the inputs $x_1,\dots,x_n$ and the earlier gates $g_1,\dots,g_{j-1}$; a gate may read the same wire several times. A circuit with $m$ outputs additionally designates $m$ wires as outputs. On an input $x\in U^n$ the gates are evaluated in order, and the circuit computes the map $U^n\to U^m$ given by the values of its output wires.

The *size* of the circuit is $s$, the number of gates (constants included unless stated otherwise); more generally, for a weight $c:\Omega\to\mathbb{N}$ the *weighted cost* is $\sum_j c(\omega_j)$. The *depth* of a wire is $0$ for inputs and $1+\max$ of the depths of its arguments for gates, and the depth of a circuit is the largest depth of an output. A *formula* is a circuit in which every gate is read at most once, i.e. a tree.

## Depends on

- [Boolean gates](../../../boolean-circuits/boolean-gate.md)
- [Boolean signature](../../../boolean-circuits/boolean-signature.md)
- [Boolean interpretation](../../../boolean-circuits/boolean-interpretation.md)
- [Arithmetic circuit](../../../../algebraic-complexity/arithmetic-circuits/arithmetic-circuit.md)

## Sources

- CSLib, `Cslib.Circuits.Circuit` (module `Cslib.Computability.Circuit.Basic`): circuits over a signature as straight-line programs with designated output wires, their evaluation, size and depth.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
