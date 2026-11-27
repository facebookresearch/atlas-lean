# A decider is a verifier with witness bound zero

Let $L$ be a decision problem and let $f$
be a timed decider whose return value on every bit string $x$ equals $L(x)$. Then the verifier
that sends an input $x$ and a witness $w$ to $f(x)$, ignoring $w$, verifies $L$ with the zero
polynomial as witness bound, so only the empty witness is allowed.

Together with the fact that this verifier has polynomial declared time whenever $f$ does, this is
the declared-time form of $\mathrm{P} \subseteq \mathrm{NP}$ for named algorithms.
