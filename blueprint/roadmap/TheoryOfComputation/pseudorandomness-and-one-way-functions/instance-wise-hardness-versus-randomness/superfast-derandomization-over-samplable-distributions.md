# Chen–Tell: superfast heuristic derandomization BPTIME[T] in heur-DTIME[n^ε·T] from uniform assumptions

Let $T$ be a polynomial. Say that a probabilistic algorithm $A$ **approximately prints** $f$ on $x$ if $\Pr[A(x)_i=f(x)_i]\ge .99$ over a uniform $i\in[k]$ and the coins of $A$. Assume one-way functions secure against uniform polynomial-time algorithms exist, and that for every $\varepsilon>0$ there are $\delta>0$ and $f\colon\{0,1\}^n\to\{0,1\}^{n^{\varepsilon}}$ such that

1. given $(x,i)\in\{0,1\}^n\times[n^{\varepsilon}]$ the $i$-th bit of $f(x)$ is computable in time $T'(n)=T(n)\cdot n^{\varepsilon}$, and
2. for every probabilistic algorithm running in time $T'(n)\cdot n^{\delta}$ and every polynomial-time samplable distribution $X$, the probability over $x\sim X$ that it approximately prints $f$ on $x$ is negligible.

Then $\mathrm{BPTIME}[T]\subseteq\bigcap_{\varepsilon>0}\mathrm{heur}_{1-\mathrm{neg}}\text{-}\mathrm{DTIME}[n^{\varepsilon}\cdot T]$: for every such language $L$ there is a deterministic algorithm of time $n^{\varepsilon}T(n)$ that, for every polynomial-time samplable distribution, errs only on a negligible fraction of inputs.

## Proof sketch

The hard string $f(x)$ is computed from the input and used as the truth table for a reconstructive Nisan–Wigderson style generator, giving pseudorandom strings for the machine on input $x$ itself. A distinguisher on many inputs yields, through the instance-wise reconstruction, an algorithm that approximately prints $f(x)$ faster than the batch bound allows. The one-way function supplies a fast seed-extending PRG so that the total overhead is only $n^{\varepsilon}$.

## Depends on

- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)

## Proof depends on

- [Targeted pseudorandom generators and targeted hitting-set generators](targeted-prg-and-targeted-hsg.md)
- [Nisan–Wigderson generator](../derandomization/nisanwigderson-generator.md)

## Sources

- Lijie Chen and Roei Tell, "Hardness vs Randomness, Revised: Uniform, Non-Black-Box, and Instance-Wise", FOCS (2021), ECCC TR21-080.
