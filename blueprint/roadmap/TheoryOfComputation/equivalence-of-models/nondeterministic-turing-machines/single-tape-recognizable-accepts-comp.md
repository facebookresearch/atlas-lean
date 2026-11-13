# Deterministic machines recognize NTM acceptance along a computable map

Let $m$ be a
single-tape nondeterministic Turing machine with a finite set of states and a finite tape alphabet
$\Sigma$ that has decidable equality and a primitive recursive encoding. Let $\alpha$ be a
primitively encodable type and $f$ a computable map from $\alpha$ to words over $\Sigma$. Then the
predicate on $\alpha$ that holds at $a$ exactly when $m$ accepts $f(a)$ is recognizable by a
single-tape deterministic Turing machine.

## Sources

- Sipser, Theorem 3.16.
