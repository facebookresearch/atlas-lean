# Every finite-state machine has a code

Let $k \in \mathbb{N}$ and let $M$ be a deterministic multi-tape Turing machine with $k$ work tapes
over the binary alphabet whose set of states is finite. Then there are a code $c$ for $k$ work
tapes and an injective map $e$ from the states of $M$ to $\mathbb{N}$ such that the machine of
$c$ simulates $M$ up to the state relabelling $e$: its initial state is $e(q_0)$, where $q_0$ is
the initial state of $M$, and its action in a state $e(q)$, for given symbols under the input and
work heads, is the action of $M$ in $q$ for the same symbols with the successor state relabelled
by $e$ (see [simulation up to a state relabelling](../../multi-tape-and-multi-stack/multi-tape-turing-machines/is-relabelling.md)).
