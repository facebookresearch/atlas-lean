# Weak ETH makes one half the infimum logarithmic exponent for exact tape multiplication

A deterministic tape machine has finitely many tapes, control states and alphabet symbols. The bit symbols are distinct, the separator and blank are distinct, and bits are neither. All heads start at cell zero. On the input tape place the two most-significant-bit-first words of equal positive length $n$, separated by one separator, starting at cell zero, with blanks elsewhere and on all other tapes. At a step the finite rule reads the symbols at all heads, writes to the scanned cells, and moves each head by $-1,0,$ or $1$; no transition means halt. At halt the designated tape contains exactly the $2n$-bit most-significant-first product from absolute cell zero and is blank elsewhere, with no final-head condition. Call $r\in\mathbb R$ achievable if there is one such machine and one natural-valued clock $W$ bounding halting on every legal input pair at every positive width, and there is a real $C>0$ with $W(n)\le C n(1+\log n)^r$ for all sufficiently large natural $n$. This clock need not be the actual maximum and there is no space hypothesis.

The hypothesis here is **power-saving Weak ETH**: there do not exist a real $0<\nu<1$, naturals $C,d$, and one finite deterministic multitape machine that correctly decides width-at-most-three CNFs on every $v$ variables, with a halting-time bound $2^{C v^{1-\nu}}(1+v+L)^d$ on each formula of encoded bit length $L$. Clauses and formulas are finite sets and the bit encoding uses unary variable count, sorted literal codes and sorted clauses with nested list framing. A literal at index $i$ with sign bit $b$ is encoded via $2i+b$. The decision machine has finite tape, alphabet and state sets, the input word on one tape and other tapes blank, and simultaneous local writes and unit head moves.

Assume power-saving Weak ETH. Then $1/2$ is the greatest lower bound in $\mathbb R$ of the set of achievable exponents. The result does not assert attainment at $1/2$ or that the set has a least element.

## Depends on

- Exact deterministic full-output tape clocks, the eventual real logarithmic bound and the stated power-saving Weak ETH predicate.

## Proof depends on

- [Near-square-root uniform multiplication](uniform-near-square-root-log-multiplication.md) for upper exponents with positive slack.
- [Conditional low-bit bound](weak-eth-randomized-low-product-tape-lower-bound.md) applied to a full-output deterministic program, with its low bits read in the prescribed interval.

## Expansion

Construct the fixed-machine bridge from full output to low-bit readout without adding an asymptotic head-traversal charge that weakens the lower bound. Convert the varying excess exponent to every fixed positive slack, and prove the greatest-lower-bound characterization without substituting an achieved minimum.

## Sources

- OpenAI, [finite multitape SAT and Weak ETH](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MultitapeWeakETH.lean#L19-L173), [tape semantics and input layout](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MultitapeWeakETH.lean#L177-L255), [exact clocks and greatest lower bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MultitapeWeakETH.lean#L387-L402).
