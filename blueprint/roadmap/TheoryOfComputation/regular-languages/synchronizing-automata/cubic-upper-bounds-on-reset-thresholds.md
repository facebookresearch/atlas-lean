# Cubic upper bounds on the reset threshold

Every [synchronizing automaton](synchronizing-automata-and-reset-words.md) with $n$ states has a reset word of length at most $\frac{n^3 - n}{6}$, so
$C(n) \le \frac{n^3 - n}{6}$ (Pin–Frankl bound). The leading coefficient has been improved slightly, first to
$C(n) \le \frac{85059 n^3 + 90024 n^2 + 196504 n - 10648}{511104}$, with leading coefficient about $0.1664$ (Szykuła), and then to
$C(n) \le \big(\frac{7}{48} + \frac{15625}{798768}\big) n^3 + o(n^3)$, with leading coefficient about $0.1654$ (Shitov). No upper bound quadratic in $n$ is known.

## Expansion

This page becomes ready once:

- The proof of the Pin–Frankl bound, which combines J.-É. Pin's reduction of the problem to a combinatorial question about finite sets with P. Frankl's solution of that question, with a source whose locators have been checked (proof prerequisite and source check; not yet stated)

## Depends on

- [Synchronizing automata and reset words](synchronizing-automata-and-reset-words.md)

## Sources

- M. V. Volkov, "List of results on the Černý conjecture and reset thresholds for synchronizing automata", arXiv:2508.15655v4, January 2026: Section 1.2, the Pin–Frankl bound (crediting J.-É. Pin and P. Frankl), the bound of M. Szykuła and the bound of Y. Shitov.
