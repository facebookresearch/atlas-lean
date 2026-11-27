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
- M. Szykuła, "Improving the upper bound on the length of the shortest reset word", *35th Symposium on Theoretical Aspects of Computer Science (STACS 2018)*, LIPIcs 96, 2018, paper 56, doi:10.4230/LIPIcs.STACS.2018.56, author version arXiv:1702.05455v5: Section 1, Theorem 1 (the Pin–Frankl compression bound, crediting Pin and Frankl, stated there for strongly connected automata) with the derivation of $(n^3 - n)/6$, and Theorem 11 (the new bound).
- Y. Shitov, "An improvement to a recent upper bound for synchronizing words of finite automata", *Journal of Automata, Languages and Combinatorics* 24(2–4), 2019, the refereed source of the bound $\big(\frac{7}{48} + \frac{15625}{798768}\big) n^3 + o(n^3)$, as credited in the survey above.
