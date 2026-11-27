# Jerrum–Valiant–Vazirani: approximate counting and almost uniform sampling are equivalent

For every relation $R\in\mathsf{PC}$ (polynomially bounded witnesses, polynomial-time membership test) that is self-reducible in Jerrum, Valiant and Vazirani's sense (in particular every one-bit self-reducible one): $|R(x)|$ has an FPRAS if and only if $R$ has a fully polynomial almost uniform generator in their sense, and equally if and only if $R$ has an FPAUS (a sampler that outputs witnesses within variation distance $\delta$ of uniform), both notions as on the linked page. Moreover, for every $R\in\mathsf{PC}$, self-reducible or not, a polynomial-time probabilistic machine with a $\#\mathsf{P}$ oracle is an exact uniform generator for $R$: it outputs only witnesses, each witness of $x$ with the same probability, and some witness with probability at least $1/2$ when $R(x)\ne\emptyset$. The failure probability cannot be removed: with fair coins and worst-case running time $T$ every output probability is a multiple of $2^{-T}$, so no such machine outputs each of $3$ witnesses with probability exactly $1/3$.

## Proof sketch

Sampling to counting: write $|R(x)|=|R(x_{\mathrm{last}})|\prod_i\frac{|R(x_{i-1})|}{|R(x_i)|}$ along a path of self-reduction steps, choosing at each step the more popular branch; each inverse ratio $|R(x_i)|/|R(x_{i-1})|$ is at least $1/2$ and is estimated by sampling. Counting to sampling: choose the bit $b$ with probability proportional to the estimated $|R(x_b)|$ and recurse, correcting the accumulated bias by rejection.

## Depends on

- [Fully polynomial almost uniform samplers and self-reducible witness families](fully-polynomial-almost-uniform-samplers.md)

## Sources

- Mark R. Jerrum, Leslie G. Valiant and Vijay V. Vazirani, "Random Generation of Combinatorial Structures from a Uniform Distribution", Theoretical Computer Science 43, 169–188, 1986, Theorems 6.3 and 6.4, and Section 2 (the definition of a uniform generator) and Theorem 3.3 for exact uniform generation.
- Mark Jerrum, "Counting, Sampling and Integrating: Algorithms and Complexity", Lectures in Mathematics ETH Zürich, Birkhäuser, 2003, Chapter 3, Section 3.1 (definition of an FPAUS, Remark 3.3 on exactly uniform sampling) and the opening of Section 3.2 ("f admits an FPRAS if and only if S admits an FPAUS" under self-reducibility).
