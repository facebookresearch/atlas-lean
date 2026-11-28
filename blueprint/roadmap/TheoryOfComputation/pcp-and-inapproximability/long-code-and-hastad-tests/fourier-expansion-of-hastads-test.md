# Fourier expansion and completeness of Håstad's 3-bit test

For folded tables $A, B$ and a projection $\pi : \beta \to \gamma$, the acceptance probability of Håstad's test with noise $\delta$ is

$$\Pr[\text{accept}] = \frac{1}{2} + \frac{1}{2} \sum_{T \subseteq \beta} (1 - 2\delta)^{|T|}\, \hat B(T)^2\, \hat A\big(\pi_2(T)\big),$$

where $\pi_2(T) = \{c \in \gamma : |\pi^{-1}(c) \cap T| \text{ is odd}\}$. If $A = \mathrm{LC}(\pi(b))$ and $B = \mathrm{LC}(b)$ for some $b \in \beta$, the test accepts with probability exactly $1 - \delta$.

## Proof sketch

Expand each table in the Fourier basis and take expectations over independent $f, g, \mu$; orthogonality of characters collapses the triple sum to the diagonal, and $\mathbb{E}[\chi_T(\mu)] = (1-2\delta)^{|T|}$. For long codes only the singletons $\{b\}$ and $\{\pi(b)\}$ carry weight.

## Depends on

- [Håstad's noisy 3-bit linear test on a projection](hastad-noisy-three-bit-linear-test.md)

## Proof depends on

- [Plancherel's identity on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/expect-mul-eq-sum-bool-fourier-coeff-mul.md)
- [Fourier inversion on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/sum-bool-fourier-coeff-mul-cube-chi.md)

## Sources

- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 2001.
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
