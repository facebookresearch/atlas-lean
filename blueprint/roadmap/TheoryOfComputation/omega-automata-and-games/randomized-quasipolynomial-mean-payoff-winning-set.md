# Randomized quasipolynomial computation of the mean-payoff winning set

A game is a nonempty finite directed graph with a nonempty set of outgoing edge occurrences at each vertex, each vertex owned by Max or Min, and each edge carrying an integer weight. Loops and parallel edges are allowed. A strategy chooses a legal outgoing edge as a function of the finite edge history and current vertex. A vertex $v$ is winning if some Max strategy ensures that for every Min strategy the liminf of the average of the first $t$ edge weights, as $t$ tends to infinity from the play started at $v$, is at least zero.

There is one finite-control three-tape machine with blank, zero and one symbols and unit head moves, and a single real $C>0$. For each game with encoded bit length $L$ there is a natural $T\le 2^{C(\log_2(L+2))^2}$. The machine halts by $T$ for every random tape; on at least a $7/8$ fraction of the $2^T$ prefixes it writes the entire winning-set indicator, from cell $0$ on tape $2$, with blank cells outside the indicator. Tape $0$ initially contains the input and the other tapes are blank. One Boolean choice is supplied per step. The input lists vertex and edge counts, the owner bits, and each edge's one-based endpoints and sign/magnitude weight. A natural $a$ is written as a unary length prefix terminated by zero followed by the little-endian binary digits of $a+1$.

## Depends on

- The game, liminf payoff, finite machine and bit-code definitions above.

## Proof depends on

- An algorithm and complete winning-set correctness analysis for the signed bit-weight model, with a joint success bound for the entire output and an all-coin runtime bound.

## Expansion

Define the occurrence-indexed total game and positional/history strategy bridge if using positional games in the proof. Extract the quasipolynomial bit bound and prove compilation to the three-tape machine, including output framing and halting on all prefixes. A winner for just one starting state or a bound only on expected runtime does not verify the contract.

## Related topics

- [Polynomial-time solvability of mean-payoff games](polynomial-time-solvability-of-mean-payoff-games.md) asks for a stronger running-time guarantee.

## Sources

- OpenAI, [RandomizedMeanPayoff.lean, game, machine and `MainClaim`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RandomizedMeanPayoff.lean#L5-L124).
