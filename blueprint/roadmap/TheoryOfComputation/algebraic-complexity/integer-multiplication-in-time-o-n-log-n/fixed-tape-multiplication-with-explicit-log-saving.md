# Fixed-tape multiplication with an explicit logarithmic saving

There exist one deterministic machine with finitely many tapes, control states and alphabet symbols and a natural constant $C$. The bit symbols are distinct, the separator and blank are distinct, and bits are neither. All heads start at cell zero. On the input tape place the two most-significant-bit-first words of equal positive length $n$, separated by one separator, starting at cell zero, with blanks elsewhere and on all other tapes. At a step the finite rule reads the symbols at all heads, writes to the scanned cells, and moves each head by $-1,0,$ or $1$; no transition means halt.

On every such pair of words, the machine halts by time

$$
C n\,\max(1,\lceil\log_2 n\rceil)^{1-2^{-182}}.
$$

At halt the designated output tape contains exactly the $2n$-bit most-significant-first product word, starting at absolute cell zero and blank everywhere else. Leading zeros are kept, and no final head location is imposed. This is a full-output all-positive-width guarantee, with no randomness or hardness hypothesis.

## Depends on

- The equal-length separated input and fixed-length absolute output conventions in the finite tape model above.

## Proof depends on

- A fixed-tape multiplication construction with the concrete exponent saving, including serialization and the cost of moving between physical tape cells at every width.

## Expansion

Give a semantics bridge for simultaneous writes, head motion, and halt to the native multitape model; preserve absolute output positions and the cost of loading and writing the full answer. Isolate the recurrence giving the explicit saving rather than replace it by a merely asymptotic exponent near one half.

## Related topics

- [Harvey–van der Hoeven integer multiplication](theorem-1-1.md) uses a zipped natural-number code and a multi-stack machine, not this physical tape interface.

## Sources

- OpenAI, [tapes and bit values](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/NearSquareRootMultiplication.lean#L16-L80), [explicit clock and endpoint](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/NearSquareRootMultiplication.lean#L129-L151).
