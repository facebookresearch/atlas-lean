# Hoza: explicit weighted PRGs for width-n length-n ROBPs with seed length O(log^2 n + log(1/ε))

For every $n$ and $\varepsilon\gt 0$ there is an explicit $\varepsilon$-WPRG for width-$n$, length-$n$ standard-order ROBPs with seed length

$$
O\bigl(\log^2 n+\log(1/\varepsilon)\bigr).
$$

This removes the $\log\log$ factors of earlier constructions and completes this line of work in the sense that any further improvement would require beating Nisan's generator already in the constant-error regime.

## Proof sketch

The proof is a variation of the reduction from moderate-error PRGs to low-error WPRGs (Cohen–Doron–Renard–Sberlo–Ta-Shma, Pyne–Vadhan) in which the independent seeds of the correction terms are replaced by samples from averaging samplers, so that the seed cost of reducing the error from $1/\mathrm{poly}(n)$ to $\varepsilon$ is only $O(\log(1/\varepsilon))$ beyond the $O(\log^2 n)$ of Nisan's generator.

## Depends on

- [Weighted pseudorandom generators (pseudorandom pseudodistributions)](weighted-pseudorandom-generators.md)

## Proof depends on

- [Cohen–Doron–Renard–Sberlo–Ta-Shma: black-box error reduction from PRGs to weighted PRGs via Richardson iteration](error-reduction-prg-to-weighted-prg.md)

## Sources

- William M. Hoza, "Better Pseudodistributions and Derandomization for Space-Bounded Computation", APPROX/RANDOM (2021), ECCC TR21-048.
