# A decidable predicate that no single-tape NTM recognizes

There is a predicate $p$ on the
natural numbers that is decidable by a single-tape deterministic Turing machine but is not
recognizable by any single-tape nondeterministic Turing machine in the model of this topic, whose
transitions cannot test for a blank.

The predicate $n = 0$ is such a predicate.

## Sources

- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage Learning, 2013, Corollary 3.18, whose half "every Turing-recognizable language is recognized by a nondeterministic machine" fails on the pinned CSLib definition; fixed upstream by leanprover/cslib#1039.
