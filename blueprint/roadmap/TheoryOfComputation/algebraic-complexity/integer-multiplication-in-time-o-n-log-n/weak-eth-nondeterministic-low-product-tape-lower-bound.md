# Weak ETH implies a sound nondeterministic deadline lower bound for the low product bits

The hypothesis here is **power-saving Weak ETH**: there do not exist a real $0<\nu<1$, naturals $C,d$, and one finite deterministic multitape machine that correctly decides width-at-most-three CNFs on every $v$ variables, with a halting-time bound $2^{C v^{1-\nu}}(1+v+L)^d$ on each formula of encoded bit length $L$. Clauses and formulas are finite sets and the bit encoding uses unary variable count, sorted literal codes and sorted clauses with nested list framing. A literal at index $i$ with sign bit $b$ is encoded via $2i+b$. The decision machine has finite tape, alphabet and state sets, the input word on one tape and other tapes blank, and simultaneous local writes and unit head moves.

For each fixed finite multitape machine whose choice set is finite and nonempty, suppose the choice at a step selects a deterministic local write/move or halt rule based only on scanned symbols and control. Use distinct bit, separator and blank symbols. Its two $n$-bit inputs are most-significant first, either separated on one tape with the standard blank initialization or inserted into two disjoint intervals of an input-independent length-dependent background configuration. The designated output interval on one tape can depend on length. A timely accepting run consumes up to $T$ transitions and uses a choice at the halting test; a schedule specifies $T+1$ choices. Its output is read on the designated interval, not necessarily blank outside it. The target is the lowest $n$ bits of the product in most-significant-first order.

Assume power-saving Weak ETH. Fix one such machine with the following soundness condition: for every $n,T$, schedule, input pair and output word, if that schedule yields a timely accepting run writing that output, the output is the exact low product word. No approximation allowance is made on accepting outputs.

There are a real $c>0$ and natural $n_0$ such that for every $n\ge n_0$ and deadline $T$, if the fraction of the $2^{2n}$ input pairs having **some** timely accepting schedule is at least $2^{-n/100}$, then $T\ge c n\sqrt{\log_2 n}$. The choice witness may depend on the input. The constants need not equal those in the randomized clause.

## Depends on

- The power-saving Weak ETH hypothesis and local tape/schedule semantics above.

## Proof depends on

- A sound-witness version of the quantitative reduction to the forbidden power-saving 3SAT algorithm; an input-dependent schedule test does not follow from an input-independent coin law alone.

## Expansion

Prove the density estimate with a schedule witness for each successful input and separate it from the global soundness condition. Preserve the soundness quantifiers at small sizes and arbitrary deadlines even though the lower bound itself is eventual.

## Sources

- OpenAI, [finite multitape SAT and Weak ETH](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MultitapeWeakETH.lean#L19-L173), [machine definitions, soundness and endpoint](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MultitapeWeakETH.lean#L177-L383).
