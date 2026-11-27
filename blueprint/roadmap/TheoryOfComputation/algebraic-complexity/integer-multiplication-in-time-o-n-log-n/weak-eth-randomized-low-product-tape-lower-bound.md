# Weak ETH implies a randomized deadline lower bound for the low product bits

The hypothesis here is **power-saving Weak ETH**: there do not exist a real $0<\nu<1$, naturals $C,d$, and one finite deterministic multitape machine that correctly decides width-at-most-three CNFs on every $v$ variables, with a halting-time bound $2^{C v^{1-\nu}}(1+v+L)^d$ on each formula of encoded bit length $L$. Clauses and formulas are finite sets and the bit encoding uses unary variable count, sorted literal codes and sorted clauses with nested list framing. A literal at index $i$ with sign bit $b$ is encoded via $2i+b$. The decision machine has finite tape, alphabet and state sets, the input word on one tape and other tapes blank, and simultaneous local writes and unit head moves.

For each fixed finite multitape machine whose choice set is finite and nonempty, suppose the choice at a step selects a deterministic local write/move or halt rule based only on scanned symbols and control. Use distinct bit, separator and blank symbols. Its two $n$-bit inputs are most-significant first, either separated on one tape with the standard blank initialization or inserted into two disjoint intervals of an input-independent length-dependent background configuration. The designated output interval on one tape can depend on length. A timely accepting run consumes up to $T$ transitions and uses a choice at the halting test; a schedule specifies $T+1$ choices. Its output is read on the designated interval, not necessarily blank outside it. The target is the lowest $n$ bits of the product in most-significant-first order.

Under the hypothesis, for each such machine there exist $c>0$ and a natural $n_0$ such that for every $n\ge n_0$ and every deadline $T$, if **some** probability law on the length-$(T+1)$ schedules, chosen independently of the uniform input pair, has probability at least $2^{-n/100}$ of a timely accepting run whose output differs from the target in at most $n/100$ positions, then

$$
T\ge c n\sqrt{\log_2 n}.
$$

The law is not required to consist of independent coins across time. For a deterministic, always-accepting and exact implementation to which this model applies, the success probability is one at any deadline bounding all its runs.

## Depends on

- The power-saving Weak ETH hypothesis and the local tape/schedule model above.

## Proof depends on

- A lower-bound reduction turning a too-fast collection of timely approximately correct runs into a forbidden power-saving 3SAT computation in the specified machine and encoding.

## Expansion

Isolate how schedules, Hamming distortion, and low-bit output are represented and how the reduction handles the input-independent layout. Prove the finite averaging and quantitative lower bound without imposing an i.i.d. schedule law, demanding exact output on all successful inputs, or claiming an unconditional lower bound.

## Related topics

- [ETH and SETH](../../fine-grained-complexity/fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md) uses different time regimes and a word-RAM, not the negated power-saving finite-machine premise here.

## Sources

- OpenAI, [finite multitape SAT and Weak ETH](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MultitapeWeakETH.lean#L19-L173), [physical tape model, schedules, accuracy and endpoint](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MultitapeWeakETH.lean#L177-L383).
