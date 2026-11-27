# Ren–Santhanam: exponential average-case hardness of MCSP yields one-way functions, with a partial converse

If no $2^{\epsilon N}$-time algorithm computes the circuit size of a uniformly random truth table of length $N$ except on a $1/2^{o(N)}$ fraction, one-way functions exist; conversely, exponentially secure weak one-way functions in DLOGTIME make MCSP hard on average for $2^{o(N)}$-size circuits.

For a truth table $tt\in\{0,1\}^{N}$ with $N=2^{n}$, let $\mathrm{Size}(tt)$ be the number of gates of a smallest circuit computing the corresponding function $\{0,1\}^{n}\to\{0,1\}$.

1. Suppose there are a constant $\epsilon>0$ and a function $q(N)=2^{o(N)}$ such that every randomized algorithm $A$ running in time $2^{\epsilon N}$ satisfies $\Pr_{tt\leftarrow U_N}[A(tt)=\mathrm{Size}(tt)]\le 1-1/q(N)$. Then there exists a one-way function.
2. Suppose there is a weak one-way function computable in DLOGTIME with security $2^{\Omega(N)}$ against circuits. Then no non-uniform algorithm of size $2^{o(N)}$ solves MCSP on a $1-2^{-o(N)}$ fraction of inputs.

These are the circuit-size analogues of the equivalence between $\mathrm{KT}$ hardness and $\mathsf{NC}^0$ one-way functions, but they are not exact converses, for two reasons: there is a loss of $2^{O(N\log\log N/\log N)}$, coming from the loose bounds on maximum circuit complexity, and item 1 yields only a polynomial-time computable one-way function, while item 2 starts from a DLOGTIME-computable one.

## Expansion

For item 1 it suffices to build a length-preserving function that no $2^{\epsilon\tilde N/10}$-time algorithm inverts except on a $1/2^{o(\tilde N)}$ fraction; a hardness-amplification step then gives a standard one-way function. The candidate maps a description of a small circuit to its truth table, padded so that its output distribution almost dominates uniform truth tables; an inverter would recover optimal circuits for most truth tables. For item 2, the weak one-way function gives a conditionally entropy-preserving PRG of stretch $\kappa M$ through the exact-security construction; its DLOGTIME randomized encoding has truth tables of noticeably smaller circuit size than random ones, using the bounds on maximum circuit complexity, so a heuristic for MCSP would distinguish its outputs from random.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Circuit complexity of a Boolean function and truth tables](../../../circuit-complexity/minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)
- [One-way functions exist](../../impagliazzo-s-five-worlds/owfexists.md)
- [Weak one-way function](../../one-way-function-transformations/weak-one-way-function.md)
- [Ren–Santhanam: exact security of weak one-way functions equals average-case circuit hardness of K^t](exact-security-weak-owfs-and-perebor-hypotheses.md)

## Proof depends on

- [Conditionally entropy-preserving pseudorandom generators from one-way functions](../../meta-complexity-and-one-way-functions/conditionally-entropy-preserving-prgs.md)
- [Degree-3 decomposable randomized encodings of log-depth computations](../../../../ComputerScience/cryptography/public-key/obfuscation-and-witness-encryption/compact-functional-encryption-to-obfuscation/nc0-randomized-encoding.md)

## Sources

- Hanlin Ren and Rahul Santhanam, "Hardness of KT Characterizes Parallel Cryptography", *36th Computational Complexity Conference (CCC 2021)*, LIPIcs, 2021, https://doi.org/10.4230/LIPIcs.CCC.2021.35 (Theorem 3, Definition 16, Theorems 73 and 74, Remark 76, Section 6).
