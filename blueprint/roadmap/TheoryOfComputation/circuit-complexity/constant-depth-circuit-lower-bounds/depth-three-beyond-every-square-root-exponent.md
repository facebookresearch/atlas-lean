# A fixed polynomial-time language exceeds every square-root exponential depth-three size bound

There exist a Boolean language $L$ on all binary words, one deterministic finite multitape machine, and positive integers $C,a$, such that on every word $w$ the machine halts with output $L(w)$ within $C(|w|+1)^a$ steps. The machine has finitely many tapes, states, and alphabet symbols, uses an injective bit encoding disjoint from blank, starts with the word on one input tape and all other tapes blank, and updates all tape heads by at most one cell in each step. The halting configuration has no next step and its state determines the answer.

For every real $A>0$ there is an $N$ such that for all $n\ge N$, every exact circuit computing $L$ on $n$ inputs has strictly more than $2^{A\sqrt n}$ gates in the following circuit class: the bottom gates are ORs of finite lists of literals or constants, each middle AND gate chooses a set of bottom gates, and the single top OR chooses a set of middle gates. Gates can be shared, empty OR is false and empty AND is true, and the counted size is the number of bottom and middle gates plus one. Inputs, negated inputs, and constants have no additional gate cost. The language and its decider are fixed before $A$; neither a fixed power improvement in the exponent nor a lower bound for all depths is part of the statement.

## Depends on

- The shared, unbounded-fan-in OR–AND–OR grammar and finite-machine model above.

## Proof depends on

- A constructive polynomial-time language and an eventual lower bound for all circuits in the specified OR–AND–OR model simultaneously at each length.

## Expansion

Prove a bridge to the native multitape model and to a circuit with explicit shared layer indices, with empty gate semantics and exact gate-count preservation. Develop the all-$A$ lower-bound estimate separately from the uniform polynomial-time recognizer.

## Sources

- OpenAI, [DepthThree.lean, circuit, machine and endpoint](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DepthThree.lean#L9-L140).
