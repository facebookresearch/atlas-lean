# Jerrum–Valiant–Vazirani: approximate counting and almost uniform sampling are equivalent

For every self-reducible relation $R\in\mathsf{PC}$ (polynomially bounded witnesses, polynomial-time membership test): $|R(x)|$ has an FPRAS if and only if $R$ has an FPAUS. Moreover an exact counting oracle gives an exact uniform generator in probabilistic polynomial time.

## Proof sketch

Sampling to counting: write $|R(x)|=|R(x_{\mathrm{last}})|\prod_i\frac{|R(x_{i-1})|}{|R(x_i)|}$ along a path of self-reduction steps, choosing at each step the more popular branch; each inverse ratio $|R(x_i)|/|R(x_{i-1})|$ is at least $1/2$ and is estimated by sampling. Counting to sampling: choose the bit $b$ with probability proportional to the estimated $|R(x_b)|$ and recurse, correcting the accumulated bias by rejection.

## Depends on

- [Fully polynomial almost uniform samplers and self-reducible witness families](fully-polynomial-almost-uniform-samplers.md)

## Sources

- Mark R. Jerrum, Leslie G. Valiant and Vijay V. Vazirani, "Random Generation of Combinatorial Structures from a Uniform Distribution", Theoretical Computer Science 43, 169–188, 1986, Theorems 6.3 and 6.4 (and Section 3 for exact counting).
