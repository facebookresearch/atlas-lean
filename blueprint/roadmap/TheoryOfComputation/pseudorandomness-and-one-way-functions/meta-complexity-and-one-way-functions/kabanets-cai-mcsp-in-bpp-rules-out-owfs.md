# Kabanets–Cai: if MCSP is in BPP, there are no one-way functions

If $\mathrm{MCSP} \in \mathsf{BPP}$, then no one-way function exists: for every function $f(y, x)$ computable in time polynomial in $|x|$ and length-preserving for each fixed $y$, some probabilistic polynomial-time algorithm, given $y$ and $f(y, x)$ for a uniform $x \in \{0,1\}^n$, finds a preimage with probability at least $1/q(n)$ for a polynomial $q$ and all large $n$. This is Allender, Buhrman, Koucký, van Melkebeek and Ronneburger's Theorem 45, which gives such an inverter with oracle access to any polynomially dense language whose strings $x$ all have $\mathrm{KT}(x) \ge |x|^{\varepsilon}$ for some $\varepsilon > 0$, together with their Section 4.2, which notes that such languages are found in $\mathsf{P}^{\mathrm{MCSP}}$, so that a $\mathsf{BPP}$ decider for $\mathrm{MCSP}$ with exponentially small error answers the oracle queries. Kabanets and Cai state the non-uniform form (their Theorem 2: if $\mathrm{MCSP} \in \mathsf{P/poly}$, there is no strong pseudorandom generator in $\mathsf{P/poly}$).

## Proof sketch

Allender et al. derive Theorem 45 from the inversion theorem of Håstad, Impagliazzo, Levin and Luby (their Theorem 44): a pseudorandom generator built from $f$ has outputs of low $\mathrm{KT}$ complexity, so the dense oracle language distinguishes it from uniform, and a distinguisher yields an inverter. The following uniform pseudorandom-function form is derived here and stated in none of the sources read: if $\mathrm{MCSP} \in \mathsf{BPP}$, then for every keyed function family $F = \{F_k : \{0,1\}^n \to \{0,1\}^n\}_{k \in \{0,1\}^n}$ with key length and input length $n$ (as in Katz–Lindell's pseudorandom functions), computable in time polynomial in $n$, some probabilistic polynomial-time oracle adversary distinguishes $F_k$ for a uniform key $k$ from a uniformly random function $\{0,1\}^n \to \{0,1\}^n$ with advantage at least $1/4$ for all large $n$, so no pseudorandom function family exists, and by the uniform construction of pseudorandom functions from one-way functions no one-way function exists either. The adversary queries the oracle on all inputs of a block of $m = O(\log n)$ bits to obtain a truth table of length $2^m$, and asks the MCSP decider whether it has circuits of size $n^c$. The truth table of $F_k$ restricted to such a block has small circuits, while a random function's truth table almost surely has circuit complexity near $2^m/m$ by counting.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Asymptotic PRF security relative to a class of distinguishers](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-functions/prfsecure.md)
- [One-way functions imply adaptively secure pseudorandom functions](../hard-core-predicates-and-stretch/one-way-functions-imply-pseudorandom-functions.md)

## Sources

- V. Kabanets and J.-Y. Cai, "Circuit Minimization Problem", Proceedings of the 32nd Annual ACM Symposium on Theory of Computing (STOC), 2000, Theorem 2.
- E. Allender, H. Buhrman, M. Koucký, D. van Melkebeek and D. Ronneburger, "Power from Random Strings", SIAM Journal on Computing 35(6), 2006, Section 4: Theorem 44 (the HILL inversion with an oracle), Theorem 45 (inversion with a dense oracle of high KT complexity) and Section 4.2 (such oracles in $\mathsf{P}^{\mathrm{MCSP}}$).
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 2nd edition, CRC Press, 2014, Definition 3.25.
