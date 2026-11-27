# Uniform tape multiplication at a near-square-root logarithmic exponent

There exist one fixed deterministic finite multitape machine, a natural-valued $W$ and a natural constant $S$ satisfying the following contract. A deterministic tape machine has finitely many tapes, control states and alphabet symbols. The bit symbols are distinct, the separator and blank are distinct, and bits are neither. All heads start at cell zero. On the input tape place the two most-significant-bit-first words of equal positive length $n$, separated by one separator, starting at cell zero, with blanks elsewhere and on all other tapes. At a step the finite rule reads the symbols at all heads, writes to the scanned cells, and moves each head by $-1,0,$ or $1$; no transition means halt. At halt the designated tape contains exactly the $2n$-bit most-significant-first product from absolute cell zero and is blank elsewhere, with no final-head condition. For each positive width $n$, every input pair reaches a halting configuration with the correct full $2n$-bit output, and $W(n)$ is the greatest of the actual halting times over these input pairs. Each run visits at most $Sn$ distinct tape/cell pairs, counting every scanned-head location from the initial through the halting configuration. Unvisited input cells are not added to the visited-set count by virtue of containing input.

There exists one real sequence $\delta(n)\to0$ such that for all sufficiently large natural $n$,

$$
W(n)\le n(1+\log n)^{1/2+\delta(n)}.
$$

The same machine serves every length and the eventual varying exponent; the statement does not assert a constant-factor bound at exponent $1/2$.

## Depends on

- The finite tape semantics and absolute-position full-product convention above.

## Proof depends on

- The uniform multiplication construction, its worst-case recurrence for a single machine and a linear visited-cell certificate along every run.

## Expansion

Prove the maximum exists and is the actual maximum for the same machine that computes the products. Separate the uniform runtime proof from the tape footprint proof, and bridge the input layout and headwise visit accounting before attributing this asymptotic to another machine model.

## Sources

- OpenAI, [NearSquareRootMultiplication.lean, `VisitsAtMost`, `haltingTimes`, `UniformWorstCaseSpec` and endpoint](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/NearSquareRootMultiplication.lean#L87-L123).
