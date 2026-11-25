# Achievable rates form an interval containing zero

Let $\Phi$ be a channel between finite-dimensional spaces. For classical communication and for quantum communication
separately: the rate $0$ is achievable, and if a rate $R$ is achievable then so is every rate $R'$ with $0 \le R' \le R$.
Hence the achievable rates form an interval with left end $0$, and the capacities $C(\Phi)$ and $Q(\Phi)$ are suprema of
nonempty sets, with $C(\Phi) \ge 0$ and $Q(\Phi) \ge 0$.

## Proof

Rate $0$: for every $n$ there is $2^{0} = 1$ message, sent as any input state and decoded by the trivial measurement with
error $0$; for quantum communication, $\lfloor 0 \cdot n \rfloor = 0$ qubits form a one-dimensional space, and the encoding and
decoding channels between it and the channel's input and output compose to the identity, at diamond distance $0$.
Monotonicity: $\lfloor R'n \rfloor \le \lfloor Rn \rfloor$. A classical code for $R$ restricted to $2^{\lfloor R'n \rfloor}$ of its messages keeps its
maximal error. For quantum communication, precede the encoding for $R$ by appending $\lfloor Rn \rfloor - \lfloor R'n \rfloor$ qubits in a fixed
state and follow the decoding by tracing them out; composing with channels does not increase the diamond norm of a difference, so
the error stays below $\varepsilon$.

## Depends on

- [Operational classical and quantum capacities](remaining-clauses-of-operational-capacity-definitions.md)

## Sources

- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018, Sections 8.1.1 and 8.1.2 (operational definitions of classical and quantum capacity). <https://cs.uwaterloo.ca/~watrous/TQI/>
