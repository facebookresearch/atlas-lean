# Chen–Tell general tradeoff: size-T depth-d hard functions give prDTIME simulations via T̄

There is a universal constant $c>1$ such that the following holds. Assume some $f\colon\{0,1\}^n\to\{0,1\}^n$ is computable by deterministic logspace-uniform circuits of size $T(n)$ and depth $d(n)$ and cannot be computed in probabilistic time $d(n)\cdot n^{c}$ on almost all inputs. Let $\bar T(m)=2^{c\cdot\log^2(T(m))/\log m}$. Then

$$
\mathrm{prRP}\subseteq\bigcup_{a\ge 1}\mathrm{prDTIME}\bigl[\bar T(n^{a})\bigr],\qquad
\mathrm{prBPP}\subseteq\bigcup_{a\ge 1}\mathrm{prDTIME}\bigl[\bar T(\bar T(n^{c\cdot a})^{a})\bigr].
$$

For polynomial $T$ both bounds are polynomial; for quasi-polynomial $T$ they are quasi-polynomial.

## Proof sketch

The proof is the same reconstruction argument with output length $M$ a fixed polynomial of the simulated machine's running time; the cost $2^{O(\log^2T/\log M)}$ of printing the Nisan–Wigderson based hitting set is exactly $\bar T$. Derandomizing two-sided error applies the one-sided simulation twice, which composes $\bar T$ with itself.

## Depends on

- [Hardness of a multi-output function on almost all inputs for probabilistic time](almost-all-inputs-hardness.md)
- [Log-space uniform circuit families](../../complexity-classes/time-and-space-complexity-classes/uniform-circuit-family.md)

## Proof depends on

- [Chen–Tell instance-wise reconstruction: a targeted HSG from a shallow logspace-uniform circuit](instance-wise-reconstruction-targeted-hsg.md)
- [Chen–Tell: prBPP = prP from almost-all-inputs hardness of depth-n² logspace-uniform circuits](prbpp-eq-prp-from-almost-all-inputs-hardness.md)

## Sources

- Lijie Chen and Roei Tell, "Hardness vs Randomness, Revised: Uniform, Non-Black-Box, and Instance-Wise", FOCS (2021), ECCC TR21-080.
