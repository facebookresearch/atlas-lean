# A deterministic refuter for small circuits against affine dispersers

There is a deterministic procedure that, given a $B_2$ circuit $C$ on $n$ inputs and (oracle access to) a Boolean function $f$, outputs an input $x\in\{0,1\}^n$ with the following guarantee: if $f$ is an affine disperser for dimension $d$ and $C$ has fewer than $4n-9d$ genuinely binary gates, then $C(x)\neq f(x)$. The procedure follows the gate-elimination steps of the $4n-9d$ lower bound to obtain an affine subspace of dimension at least $d$ on which $C$ is constant, and then searches its $2^d$ points.

## Proof sketch

Each gate-elimination step is constructive: it selects a restriction, computable from the circuit, that preserves the invariants. At a terminal state the circuit computes an affine function or a constant on a subspace of dimension at least $d$, where the disperser is nonconstant; enumerating the subspace finds a disagreement.

## Depends on

- [Affine dispersers](affine-dispersers.md)

## Proof depends on

- [A 4n - 9d lower bound for affine dispersers](affine-disperser-4n-minus-9d-lower-bound.md)

## Sources

- Om Swostik Mishra, Rahul Santhanam, "An Explicit 4n - O(\log n) Size Lower Bound against General Boolean Circuits", 2027.
