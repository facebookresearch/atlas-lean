# Heavy element avoidance problem

Heavy Avoid asks, given a sampler for a distribution on $N$-bit strings and a threshold $\delta(N)\ge 1/\mathrm{poly}(N)$, for an $N$-bit string of probability less than $\delta(N)$. It is a total search problem that random guessing solves, yet deterministic algorithms for it are tied to frontier lower bounds and derandomization.

Let $D$ be a distribution on $\{0,1\}^N$. A string $y$ is $\delta$-heavy in $D$ if $\Pr_{z\sim D}[z=y]\ge\delta$, and $\delta$-light otherwise. Heavy Avoid with threshold $\delta$ asks for a $\delta$-light string.

- **Uniform version.** For an ensemble $\mathcal{D}=\{D_N\}_{N\ge 1}$ sampled by a uniform sequence of circuits from a class $\mathcal{C}$, $(\mathcal{D},\delta)$-Heavy-Avoid is the problem of finding, given $1^N$, a $\delta(N)$-light element of $D_N$.
- **Non-uniform version.** The algorithm receives a circuit sampler from $\mathcal{C}$ as input.
- **Implicit and explicit samplers.** An explicit sampler $C(r)$ outputs the whole $N$-bit sample from randomness $r$, so its size is at least $N$; an implicit sampler $C(r,i)$ outputs the $i$-th bit of the sample, for $i\in[N]$, and is typically smaller than $N$. Implicit-$\delta$-Heavy-Avoid is the non-uniform problem for implicit samplers.

Basic facts, for $\delta(N)\ge 1/\mathrm{poly}(N)$ and $\delta>2^{-N}$:

1. At most $1/\delta$ strings are $\delta$-heavy, so the problem is total and one of the lexicographically first $\lceil 1/\delta\rceil+1$ strings is always a solution.
2. A uniformly random $N$-bit string is a solution except with probability at most $(1/\delta)2^{-N}$.
3. The complementary problem Heavy Find, outputting a $\delta$-heavy string when a $2\delta$-heavy one exists, has a simple randomized algorithm, and a deterministic polynomial-time algorithm for it is equivalent to $\mathsf{prBPP}=\mathsf{prP}$.
4. If a deterministic algorithm solves Implicit-$\delta$-Heavy-Avoid for some $\delta(N)=o(1)$ on implicit samplers of size $N^{\epsilon}$, and is implementable by logspace-uniform circuits of size $\mathrm{poly}(N)$ and depth $N^{o(1)}$, then $\mathsf{prBPP}=\mathsf{prP}$.

## Expansion

For fact 3, a probabilistic machine $M$ with error at most $1/4$ on input $x$ defines a sampler that outputs $1^N$ when $M$ accepts on randomness $r$ and $0^N$ otherwise; the unique $1/3$-heavy string is the majority answer. Fact 4 is a non-black-box argument: it uses the Chen–Tell instance-wise hitting set generator for low-depth circuits, in which the reconstruction procedure of the generator and the assumed Heavy Avoid algorithm together define a function that is hard on almost all inputs. For explicit polynomial-time samplers, a polynomial-time pseudodeterministic algorithm that behaves pseudodeterministically on every length would give $\mathsf{BPE}\not\subseteq\mathsf{BPTIME}[2^{kn}]$ for every $k$, a long-open probabilistic time hierarchy.

## Depends on

- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Proof depends on

None.

## Sources

- Zhenjian Lu, Igor C. Oliveira, Hanlin Ren and Rahul Santhanam, "On the Complexity of Avoiding Heavy Elements", *65th IEEE Symposium on Foundations of Computer Science (FOCS 2024)*, 2024, https://doi.org/10.1109/FOCS61266.2024.00140 (Sections I and II, Theorem II.6, Proposition II.5, Section III).
