# Rudich's conjecture

Rudich's conjecture says that, for some constant $c$, every language decided by polynomial-size nondeterministic circuits that contains only truth tables of functions without circuits of size $n^c$ is very sparse: it holds at most a $1/N^{\omega(1)}$ fraction of the strings of length $N$ for every sufficiently large $N$.

Given a string $y$ of length $N$, $\mathrm{fn}(y)$ is the Boolean function on $n = \lfloor \log N \rfloor$ bits whose truth table is the initial $2^n$-bit prefix of $y$, and for a size function $s$, $\mathrm{MCSP}[s]$ is the set of strings $y$ such that $\mathrm{fn}(y)$ has Boolean circuits of size at most $s(n)$; $\overline{\mathrm{MCSP}[s]}$ is its complement. The $N$-slice of a language $L$ is $L_N = L \cap \{0,1\}^N$, and for $\epsilon \colon \mathbb{N} \to [0,1]$ the language $L$ is $\epsilon$-sparse if $|L_N|/2^N \le \epsilon(N)$ for every large enough $N$. $\mathsf{NSIZE}(\mathrm{poly})$ is the class of languages decided by nondeterministic circuits of polynomial size.

**Rudich's conjecture.** There is a constant $c > 0$ such that for every language $L$, if $L \subseteq \overline{\mathrm{MCSP}[n^c]}$ and $L \in \mathsf{NSIZE}(\mathrm{poly})$, then $L$ is $1/N^{\omega(1)}$-sparse.

## Context

Equivalently, for every proof system verifiable by polynomial-size circuits, all but a $1/N^{\omega(1)}$ fraction of truth tables of length $N$ have no $\mathrm{poly}(N)$-size proofs that their circuit complexity exceeds $n^c$. Rudich stated the conjecture in the language of natural proofs, as a strengthening of the Razborov–Rudich barrier from deterministic to nondeterministic properties; it is a zero-error average-case hardness hypothesis for MCSP against nondeterministic circuits under the uniform distribution.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Circuit complexity of a Boolean function and truth tables](../../../circuit-complexity/minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)

## Proof depends on

None.

## Sources

- Ján Pich and Rahul Santhanam, "Why are Proof Complexity Lower Bounds Hard?", *FOCS* 2019, DOI 10.1109/FOCS.2019.00080 (Rudich's Conjecture, Definition 6 of MCSP[s] and the definitions of slices and sparsity, Section 2.3; the informal statement in Section 1.2; in the authors' full version of 5 April 2019, <https://ora.ox.ac.uk/objects/uuid:b038d171-928d-4dfe-abf5-a6fdb03217b2>).
- Steven Rudich, "Super-bits, demi-bits, and NP/qpoly-natural proofs", in *RANDOM '97*, Lecture Notes in Computer Science, Springer, 1997, pp. 85–93, DOI 10.1007/3-540-63248-4_8.
