# Eight-symbol fair-bit Post–Turing execution and output

Use one bidirectional tape with symbols $0,\ldots,7$ and blank symbol $0$, and finitely many states numbered starting at zero. The head starts on the first input symbol (or on a blank for the empty input); the input word is to its right including the scanned cell, and the rest of the tape is blank. In each nonhalted configuration the transition table reads the current state, scanned symbol, and one bit. It either detects halt without modifying the tape, or changes state and performs **one** operation: move the head one cell left or right, or write a symbol into the current cell without moving. Halt is absorbing. A length-$t$ prefix runs exactly $t$ ticks, whether or not halt was detected earlier. Under the fair law each of the $2^t$ prefixes has mass $2^{-t}$.

A word is output only with absent control state (halted) and with the right semi-tape **including the current cell** equal to that word padded by blanks (`Turing.ListBlank.mk`); there is no requirement on the left semi-tape. A natural numeral uses its low-to-high `Nat.bits` with false/true replaced by $1/2$, then a $3$ delimiter. A signed integer uses $5$ for a negative sign or $4$ otherwise, followed by the numeral for its magnitude. A rational uses its reduced signed numerator followed by the numeral for its positive denominator. A matrix output concatenates these natural-numeral words in row-major order with known dimensions. The matrix convention uses the same halted equality, not merely a prefix of a longer nonblank tape. Counting inputs also use the rational encoding; sampling inputs use only the natural fields specified in each result. Do not identify this tick with a multi-stack block step or assume a bridge to another probabilistic time model.

## Depends on

- A single-tape `Turing.TM0.Stmt` action, a finitely specified transition table conditional on a bit, and the uniform finite-prefix law.

## Expansion

Adopt the same tape initialization and head-inclusive output when formalizing the probability space. Keep the actual transition and output encoding; generalization to another machine model needs a separate agreement statement.

## Sources

- [Eight-symbol alphabet, explicit tape and halted rational output](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatchingFPRAS.lean#L25-L89)
- [The common tape semantics in the table comparator](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContingencyTables.lean#L7-L54)
- [Margin and output encodings and finite-prefix probabilities](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContingencyTables.lean#L103-L143)
