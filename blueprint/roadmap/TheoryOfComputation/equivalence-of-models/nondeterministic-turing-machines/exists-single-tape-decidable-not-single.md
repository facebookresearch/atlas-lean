# A decidable predicate that no single-tape NTM recognizes

There is a predicate $p$ on the
natural numbers that is decidable by a single-tape deterministic Turing machine but is not
recognizable by any single-tape nondeterministic Turing machine.

The predicate $n = 0$ is such a predicate.

## Sources

- Sipser, Corollary 3.18, whose half "every Turing-recognizable language is recognized by a nondeterministic machine" fails on the pinned CSLib definition; fixed upstream by leanprover/cslib#1039.
