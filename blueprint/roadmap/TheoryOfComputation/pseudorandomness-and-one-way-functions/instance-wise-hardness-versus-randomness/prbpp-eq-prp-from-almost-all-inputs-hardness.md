# Chen–Tell: prBPP = prP from almost-all-inputs hardness of depth-n² logspace-uniform circuits

There is a universal constant $c>1$ such that the following holds. Suppose there is a function $f\colon\{0,1\}^n\to\{0,1\}^n$ computable by deterministic logspace-uniform circuits of polynomial size and depth $n^2$ such that $f$ cannot be computed in probabilistic time $n^{c}$ on almost all inputs. Then $\mathrm{prBPP}=\mathrm{prP}$.

The depth $n^2$ may be replaced by any fixed polynomial depth $n^{k}$ at the cost of a larger constant $c=c_k$. The derandomization is non-black-box: the deterministic simulation of a probabilistic machine on input $x$ uses $x$ to build its pseudorandom strings.

## Proof sketch

Apply the instance-wise reconstruction to $f$ with $M=n^{O(1)}$: for each input $x$ the set $H_x$ is computable in polynomial time, and any $\mathrm{poly}(n)$-time distinguisher that has access to $x$ and avoids $H_x$ would yield a probabilistic algorithm computing $f(x)$ in time $n^{c}$. Since $f$ fails on every long input, $H_x$ is a targeted hitting set for all such tests, giving $\mathrm{prRP}=\mathrm{prP}$. Two-sided error is reduced to one-sided error with respect to the same input, using that the hardness holds instance by instance; this yields $\mathrm{prBPP}=\mathrm{prP}$.

## Depends on

- [Hardness of a multi-output function on almost all inputs for probabilistic time](almost-all-inputs-hardness.md)
- [Deterministic logarithmic space](../../complexity-classes/time-and-space-complexity-classes/log-space.md)
- [Log-space uniform circuit families](../../complexity-classes/time-and-space-complexity-classes/uniform-circuit-family.md)

## Proof depends on

- [Chen–Tell instance-wise reconstruction: a targeted HSG from a shallow logspace-uniform circuit](instance-wise-reconstruction-targeted-hsg.md)
- [Targeted pseudorandom generators and targeted hitting-set generators](targeted-prg-and-targeted-hsg.md)

## Sources

- Lijie Chen and Roei Tell, "Hardness vs Randomness, Revised: Uniform, Non-Black-Box, and Instance-Wise", FOCS (2021), ECCC TR21-080.
