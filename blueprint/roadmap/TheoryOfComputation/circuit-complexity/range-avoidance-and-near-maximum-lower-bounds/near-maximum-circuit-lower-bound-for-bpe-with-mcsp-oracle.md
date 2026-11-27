# Near-maximum circuit lower bound for BPE with an MCSP oracle and subexponential advice

For every $\varepsilon>0$, randomized exponential time with an MCSP oracle and $2^{\varepsilon n}$ bits of advice contains a language without circuits of size $2^n/n$; the proof relativizes a pseudodeterministic generator to the MCSP oracle.

Let $\mathrm{MCSP}$ be the minimum circuit size problem: given the length-$N$ truth table of $f:\{0,1\}^{\log N}\to\{0,1\}$ and a size $s$, decide whether $f$ has a circuit of size $s$. For every constant $\varepsilon>0$,

$$
\mathsf{BPE}^{\mathrm{MCSP}}/2^{\varepsilon n}\not\subseteq\mathrm{SIZE}[2^n/n].
$$

For comparison, every function has circuits of size $(1+o(1))2^n/n$, and $\mathsf{E}/2^n$ trivially contains a language of maximum circuit complexity; the advice here is only $2^{\varepsilon n}$ for arbitrarily small $\varepsilon$.

## Expansion

The Lu–Oliveira–Santhanam pseudodeterministic PRG with seed length $n^{\varepsilon}$ and one advice bit, which infinitely often fools uniform polynomial-time algorithms, is $\mathsf{PSPACE}$-relativizing; since $\mathrm{MCSP}\in\mathsf{PSPACE}$, it holds relative to $O=\mathrm{MCSP}$. Its relativized form gives $G:\{0,1\}^{N^{\varepsilon/2}}\to\{0,1\}^{N}$ computable in randomized polynomial time with an MCSP oracle and one advice bit that fools, infinitely often, every polynomial-time algorithm with an MCSP oracle. Take the test that uses the oracle to check whether a truth table of length $N=2^n$ has circuit complexity at least $2^n/n$; most truth tables pass, so some seed $z$ makes $G(z)$ pass. The language that, on $x\in\{0,1\}^n$ with advice $(z,\alpha)$ of length about $2^{\varepsilon n/2}+1$, outputs the $x$-th bit of $G(z)$ is in $\mathsf{BPE}^{\mathrm{MCSP}}/2^{\varepsilon n}$ and has no circuits of size $2^n/n$.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Circuit complexity of a Boolean function and truth tables](../minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)

## Proof depends on

- [Bounded relativization](../../hierarchy-theorems-and-barriers/relativization-and-oracle-separations/bounded-relativization.md)
- [Lu–Oliveira–Santhanam pseudodeterministic PRG](../../randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/pseudodeterministic-algorithms/lu-oliveira-santhanam-pseudodeterministic-prg.md)

## Sources

- Shuichi Hirahara, Zhenjian Lu and Hanlin Ren, "Bounded Relativization", *38th Computational Complexity Conference (CCC 2023)*, LIPIcs, 2023, https://doi.org/10.4230/LIPIcs.CCC.2023.6 (Theorem 4 with its proof idea in Section 1.2, Theorem 25, Theorem 29 and Lemmas 30 and 31, Section 3.2).
