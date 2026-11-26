# Liu–Pass: prBPP = prP iff conditional Kt gap problems are hard on every long auxiliary input

For all sufficiently large constants $c$, the following are equivalent:

1. $\mathrm{prBPP}=\mathrm{prP}$.
2. For every probabilistic algorithm $M$ running in time $n^{c}$ and every sufficiently long $z\in\{0,1\}^n$, there is $x\in\{0,1\}^n$ such that $M(\cdot,z)$ fails to decide whether $\mathrm{Kt}(x\mid z)\ge n-1$ or $\mathrm{Kt}(x\mid z)\le O(\log n)$, that is, $(x,z)$ lies in the promise of the gap problem and $M(x,z)$ errs with probability more than $1/3$.

This is a full characterization of $\mathrm{prBPP}=\mathrm{prP}$ by the hardness of a single explicit problem.

## Proof sketch

(1 to 2) Under $\mathrm{prBPP}=\mathrm{prP}$, Goldreich's construction gives a targeted PRG with target $z$ whose outputs are printed deterministically from $z$ and short seeds, hence have $\mathrm{Kt}(\cdot\mid z)=O(\log n)$, while a random $x$ has $\mathrm{Kt}(x\mid z)\ge n-1$ with high probability. An $M$ solving the gap problem for $z$ would distinguish the targeted PRG from uniform. (2 to 1) As in Hirahara's hitting-set generator, the first $O(\log n)$ seed bits select a short program, which is run on the target $z$ to obtain a hard string fed into the Impagliazzo–Wigderson generator; a distinguisher with target $z$, combined with the reconstruction, decides the conditional Kt gap problem on all $x$, so hardness yields a targeted hitting-set generator and hence derandomization.

## Depends on

- [Conditional Levin–Kolmogorov complexity Kt(x | z) and the gap problem GapMcKtP](conditional-levin-kt-gap-problem.md)

## Proof depends on

- [Targeted pseudorandom generators and targeted hitting-set generators](targeted-prg-and-targeted-hsg.md)
- [Impagliazzo-Wigderson: exponential circuit hardness in E derandomizes BPP](../nisan-wigderson.md)

## Sources

- Yanyi Liu and Rafael Pass, "Characterizing Derandomization Through Hardness of Levin-Kolmogorov Complexity", CCC (2022), ECCC TR22-084.
