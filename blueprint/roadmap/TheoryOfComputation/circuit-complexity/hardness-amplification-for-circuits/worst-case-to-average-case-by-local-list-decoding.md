# Worst-case to average-case hardness by local list decoding

Let $f:\{0,1\}^n\to\{0,1\}$, let $\mathbb{F}$ be a field with $2^w$ elements, let $H\subseteq\mathbb{F}$ and $\ell\ge1$ with $|H|^\ell\ge 2^n$, and view the truth table of $f$ as a function on $H^\ell$ (padded with zeros). Let $p:\mathbb{F}^\ell\to\mathbb{F}$ be its low-degree extension, of degree at most $|H|-1$ in each variable and so of total degree $D\le\ell(|H|-1)$, and let the *encoding* $\hat f$ be $p$ concatenated with the Hadamard code: $\hat f(y,r)=\langle\mathrm{bits}(p(y)),r\rangle\bmod 2$ for $y\in\mathbb{F}^\ell$ and $r\in\{0,1\}^w$. If $|\mathbb{F}|\ge\mathrm{poly}(D/\varepsilon)$ and some circuit of size $S$ agrees with $\hat f$ on a $\tfrac12+\varepsilon$ fraction of inputs, then $f$ has a circuit of size $\mathrm{poly}(S,D,w,1/\varepsilon)$. Consequently (taking $|\mathbb{F}|=\mathrm{poly}(S(n))$, $\ell=O(n/\log S(n))$ variables and $\varepsilon=S(n)^{-\Omega(1)}$, so that $\hat f$ has $O(n)$ input bits), if $f\in\mathsf{E}$ has worst-case hardness $H_{\mathrm{wrs}}(f)(n)\ge S(n)$, then some $g\in\mathsf{E}$ has $H_{\mathrm{avg}}(g)(n)\ge S(n/c)^{1/c}$ for a constant $c$ and all large $n$; in particular worst-case hardness $2^{\gamma n}$ in $\mathsf{E}$ gives average-case hardness $2^{\gamma' n}$ in $\mathsf{E}$ for a constant $\gamma'>0$.

## Proof sketch

Goldreich–Levin decoding turns a predictor for $\hat f$ into a list of candidates for $p$ that are correct on a noticeable fraction of points; Reed–Muller local list decoding (interpolation along random lines or curves) followed by self-correction recovers $p$, hence $f$, everywhere, with nonuniform advice selecting the right list element.

## Depends on

- [Average-case hardness against circuits](average-case-hardness-against-circuits.md)
- [Low-degree extensions with individual degree |H| - 1](../../../InformationTheory/error-correcting-codes/reed-muller-codes-and-local-decoding/low-degree-extension-individual-degree.md)
- [Local decoding of the Hadamard code](../../../InformationTheory/error-correcting-codes/hadamard-code-local-decoding.md)
- [The class E](../../complexity-classes/time-and-space-complexity-classes/e.md)

## Proof depends on

- [Goldreich-Levin: hardcore predicate from one-way permutations](../../pseudorandomness-and-one-way-functions/goldreich-levin-theorem/goldreich-levin.md)
- [Worst-case to average-case encodings stay in E](../../pseudorandomness-and-one-way-functions/average-case-complexity/distributional-reductions/worst-case-to-average-case-encoding-in-e.md)
- [Local list decoding of Reed-Muller codes along lines with advice](../../../InformationTheory/error-correcting-codes/reed-muller-codes-and-local-decoding/local-list-decoding-of-reed-muller-codes.md)
- [Goldreich–Levin list decoding of the Hadamard code with oracle access](../../pseudorandomness-and-one-way-functions/hard-core-predicates-and-stretch/goldreich-levin-list-decoding.md)

## Sources

- Madhu Sudan, Luca Trevisan, Salil Vadhan, "Pseudorandom Generators without the XOR Lemma", Journal of Computer and System Sciences 62(2), 2001.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009 (local list decoding and worst-case to strong average-case hardness; Theorem 17.31 in the 2007 web draft).
