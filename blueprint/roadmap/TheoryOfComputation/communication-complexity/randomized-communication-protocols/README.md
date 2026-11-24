# Randomized communication protocols

A public-coin protocol is a family of deterministic protocols indexed by a shared random string
drawn uniformly from a nonempty finite set; its cost is the largest depth of a member and its error on an
input pair is the fraction of random strings on which it answers wrongly. For equality of
$n$-bit strings, hashing both inputs with a shared random function to $k$ bits gives a protocol
of cost $k + 1$ that never errs on equal inputs and errs with probability exactly $2^{-k}$ on
distinct ones, whereas every deterministic protocol needs $n + 1$ bits.

More generally a randomized protocol is a finitely supported probability distribution on
deterministic protocols, and $R_\varepsilon(f)$ is the least cost of one whose error is at most
$\varepsilon$ on every input. Yao's minimax principle for communication identifies
$R_\varepsilon(f)$ with the largest, over input distributions $\mu$, of the distributional
complexity $D^\mu_\varepsilon(f)$, the least depth of a deterministic protocol with error at most
$\varepsilon$ under $\mu$; this is how lower bounds on randomized communication are proved.
Newman's theorem says that for $0 < \varepsilon \le 1/2$ private
coins cost at most $\log_2(n/\varepsilon^2) + O(1)$ extra bits, at the price of doubling the
error, which gives equality an $O(\log n)$-bit private-coin
protocol. The presentation follows A. Rao and A. Yehudayoff, *Communication Complexity* (early
draft), Chapter 3. The randomized complexity of set disjointness is linear (Kalyanasundaram and
Schnitger; Razborov); Alon, Matias and Szegedy derive from it that
approximating the largest multiplicity of a data stream needs linear memory.

- [Public-coin randomized protocol](public-coin-protocol.md)
- [Cost of a public-coin protocol](public-coin-protocol-cost.md)
- [Error probability of a public-coin protocol](error-prob.md)
- [Each run costs at most the cost](depth-le-cost.md)
- [Collision count of a uniformly random function](card-filter-apply-eq-apply-mul.md)
- [Random-hash protocol for equality](eq-hash-protocol.md)
- [Output of the random-hash protocol](eval-eq-hash-protocol.md)
- [Cost of the random-hash protocol](cost-eq-hash-protocol-le.md)
- [No error on equal inputs](error-prob-eq-hash-protocol-self.md)
- [Error of the random-hash protocol for equality](error-prob-eq-hash-protocol-of-ne.md)
- [Randomized protocol](randomized-protocol.md)
- [Cost of a randomized protocol](randomized-protocol-cost.md)
- [Error of a randomized protocol](randomized-protocol-error.md)
- [A public-coin protocol as a randomized protocol](to-randomized.md)
- [The two notions of error agree](error-to-randomized.md)
- [Cost of the induced randomized protocol](cost-to-randomized-le.md)
- [Randomized communication complexity](rand-complexity.md)
- [Randomized communication complexity of equality](rand-complexity-eq-fn-le.md)
- [Error indicator of a protocol](error-indicator.md)
- [Distributional error of a deterministic protocol](dist-error.md)
- [Distributional communication complexity](dist-complexity.md)
- [Distributional complexity is at most randomized complexity](dist-complexity-le-rand-complexity.md)
- [Yao's minimax principle for communication complexity](rand-complexity-eq-i-sup-dist-complexity.md)
- [Error probability of a private-coin protocol](private-error-prob.md)
- [Newman's theorem](newman-private-coins.md)
- [Set intersection function](disj-fn.md)
- [Randomized communication complexity of disjointness](rand-complexity-disj-fn-ge.md)

## Related topics

- [Deterministic communication protocols](../deterministic-communication-protocols/README.md): the deterministic model these protocols randomize, and the $n + 1$ lower bound for equality.
- [Yao's minimax principle](../../randomized-and-quantum-complexity/yao-s-minimax-principle/README.md): the same principle for finitely many algorithms and inputs with arbitrary costs.
- [Frequency moments of data streams](../../../ComputerScience/randomized-algorithms/frequency-moments-of-data-streams/README.md): streaming space lower bounds obtained from the disjointness bound, the memory content being the message.
