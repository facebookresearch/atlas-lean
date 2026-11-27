# Chen–Tell instance-wise reconstruction: a targeted HSG from a shallow logspace-uniform circuit

Let $f\colon\{0,1\}^n\to\{0,1\}^n$ be computed by logspace-uniform circuits of size $T=T(n)$ and depth $d=d(n)$, and let $M=M(n)$ be an output length with $c\log T\le M<T^{1/c}$, where $c>1$ is a universal constant. There is a deterministic algorithm $H$ that on input $x\in\{0,1\}^n$ prints a set $H_x\subseteq\{0,1\}^M$, and a probabilistic oracle algorithm $R$, with the following guarantee for **each fixed** $x$: if $D$ is any deterministic algorithm with $\Pr_{r\in\{0,1\}^M}[D(x,r)=1]\ge 1/2$ and $D(x,s)=0$ for all $s\in H_x$, then $R^{D(x,\cdot)}(x)$ outputs $f(x)$ with probability at least $1-1/M$ in time $(d+n^{c})\cdot\mathrm{poly}(M)$ (plus the time of the oracle calls). The set $H_x$ is printed in time $2^{O(\log^2 T/\log M)}$, which is polynomial in $T$ whenever $M\ge T^{\Omega(1)}$.

Consequently, if $f$ is hard for probabilistic time $(d+n^{c})\cdot\mathrm{poly}(M)$ on the input $x$, then $H_x$ hits every dense property that a deterministic algorithm with access to $x$ decides in time $\mathrm{poly}(M)$.

## Proof sketch

Following the doubly-efficient proof system of Goldwasser, Kalai and Rothblum, the computation of $f(x)$ is written as a sequence of $d'=d\cdot\mathrm{polylog}(T)$ low-degree polynomials $P^x_i\colon\mathbb{F}^m\to\mathbb{F}$ over a field of size $M^{O(1)}$, with $m=O(\log T/\log M)$ and degree at most $M$; $P^x_1$ is computable from $x$ in time $\mathrm{poly}(M)$, each $P^x_i$ is computable from oracle access to $P^x_{i-1}$ in time $\mathrm{poly}(M)$ (downward self-reducibility), and $f(x)$ is read off $P^x_{d'}$. The set $H_x$ is the union of Nisan–Wigderson generator outputs instantiated with the truth tables of all $P^x_i$. A distinguisher that avoids $H_x$ lets the Impagliazzo–Wigderson style uniform learner reconstruct $P^x_{i}$ layer by layer from $P^x_{i-1}$, using random self-reducibility of low-degree polynomials to correct errors, and finally evaluates $P^x_{d'}$.

## Depends on

- [Targeted pseudorandom generators and targeted hitting-set generators](targeted-prg-and-targeted-hsg.md)
- [Log-space uniform circuit families](../../complexity-classes/time-and-space-complexity-classes/uniform-circuit-family.md)

## Proof depends on

- [Nisan–Wigderson generator](../derandomization/nisanwigderson-generator.md)
- [Impagliazzo-Wigderson: exponential circuit hardness in E derandomizes BPP](../nisan-wigderson.md)

## Sources

- Lijie Chen and Roei Tell, "Hardness vs Randomness, Revised: Uniform, Non-Black-Box, and Instance-Wise", FOCS (2021), ECCC TR21-080.
- Lijie Chen, Zhenjian Lu, Igor C. Oliveira, Hanlin Ren and Rahul Santhanam, "Polynomial-Time Pseudodeterministic Construction of Primes", FOCS (2023), arXiv:2305.15140.
