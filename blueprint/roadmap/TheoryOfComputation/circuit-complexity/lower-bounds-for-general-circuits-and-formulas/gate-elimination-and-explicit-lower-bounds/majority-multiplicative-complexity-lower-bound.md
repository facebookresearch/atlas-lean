# Majority has multiplicative complexity at least n - B(n)

Let $B(n)$ be the number of ones in the binary representation of $n$ and let $\mathrm{MAJ}_n(x)=[\,|x|\ge\lceil n/2\rceil\,]$ (ties accepted when $n$ is even). Every circuit over a Boolean basis of fan-in at most two computing $\mathrm{MAJ}_n$ contains at least $n-B(n)$ non-affine gates; equivalently $M(\mathrm{MAJ}_n)\ge n-B(n)$ over the Zhegalkin basis.

## Proof sketch

Some Fourier coefficient of $(-1)^{\mathrm{MAJ}_n}$ has $2$-adic valuation $-(n-B(n))$ (it is a binomial-coefficient expression whose odd part is controlled by Kummer's theorem), while a circuit with $m$ non-affine gates has all coefficients in $2^{-m}\mathbb{Z}$.

## Depends on

- [The Zhegalkin basis and multiplicative complexity](../../circuit-models-and-classes/circuit-models-and-complexity-measures/zhegalkin-basis-and-multiplicative-complexity.md)
- [Majority function](../../../../Combinatorics/boolean-functions/majority-is-least-stable-conjecture/majority.md)

## Proof depends on

- [Fourier norm is at most 2^m for circuits with m nonlinear gates](fourier-norm-bounded-by-nonlinear-gates.md)

## Sources

- Anastasiya Chistopolskaya, Vladimir V. Podolskii, "Parity Decision Tree Complexity is Greater Than Granularity", 2018.
