# The rank property is P/poly-natural and useful against AC0[2]

The rank property $\mathcal{R}=(\mathcal{R}_n)$ is (i) *large*: at least half of all functions on $n$ bits satisfy it; (ii) *constructive*: membership of a truth table of length $N=2^n$ is decided by De Morgan circuits of size $O(N^3)$, and the rank is even computable in $\mathsf{NC}^2$; (iii) *useful against $\mathsf{AC}^0[2]$*: for every depth $d$ and polynomial size bound, for large $n$ no function in $\mathcal{R}_n$ has $\mathsf{AC}^0[2]$ circuits of depth $d$ and that size. Thus Razborov's lower bound is an $\mathsf{NC}^2$-natural (in particular $\mathsf{P}/\mathsf{poly}$-natural) proof in the sense of Razborov and Rudich.

## Proof sketch

Largeness: $Z_a(f)+Z_a(f\oplus\mathbb{1}_{|x|_0=a})=I$, so one of $f$ and its partner passes the test, and the pairing is an involution; hence at least half of all functions pass. Constructivity: compute the zero-sum matrix and its rank by Gaussian elimination. Usefulness: the approximation argument of the middle-slice lower bound.

## Depends on

- [Razborov's GF(2) rank property of truth tables](razborov-gf2-rank-property.md)
- [Natural property](../../../hierarchy-theorems-and-barriers/natural-proofs-barrier/natural-property.md)
- [Usefulness of a property against constant-depth circuit classes](usefulness-against-constant-depth-classes.md)

## Proof depends on

- [Razborov's rank method: the middle slice is not in AC0[2]](middle-slice-not-in-ac0-2.md)
- [Polynomial-size circuits for the rank over GF(2)](../../parallel-circuit-hierarchies/circuits-for-rank-over-gf2.md)

## Sources

- Alexander A. Razborov, Steven Rudich, "Natural Proofs", Journal of Computer and System Sciences 55(1), 1997 (Section 3.2: the rank property is $\mathsf{NC}^2$-natural with density at least $1/2$).
- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets, Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
