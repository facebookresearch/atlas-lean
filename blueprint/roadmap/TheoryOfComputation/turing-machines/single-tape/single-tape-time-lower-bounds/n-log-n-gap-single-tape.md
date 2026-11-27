# Hennie–Trakhtenbrot–Kobayashi: single-tape machines in time o(n log n) decide only regular languages

Every language decided by a deterministic single-tape Turing machine in time $o(n\log n)$ is regular (Trakhtenbrot; Hartmanis; Kobayashi, extending Hennie's linear-time result), and the bound is tight: $\{0^k1^k\}$ is decidable in time $O(n\log n)$. The argument gives an explicit threshold: if a machine with state set $Q$ decides $L$ within time $T(n)\le\frac{n\lfloor\log_2n\rfloor}{8d}$ for all large $n$, where $d=\lceil\log_2(|Q|+2)\rceil$, then $L$ is regular (this constant is a direct accounting of Kobayashi's counting argument, not printed in the sources).

## Proof sketch

If some crossing sequence were long, take a shortest input forcing a crossing sequence of length $\ge h$; using cut and paste one can remove segments between boundaries with equal crossing sequences, contradicting minimality unless the total time is $\Omega(n\log n)$. Hence all crossing sequences are bounded by a constant, and a machine with bounded crossing sequences is simulated by a two-way, hence one-way, finite automaton.

## Depends on

- [Crossing sequences of single-tape Turing machines](crossing-sequences.md)

## Sources

- F. C. Hennie, "One-tape, off-line Turing machine computations", Information and Control 8(6), 553–578, 1965, Theorem 2 (bounded crossing sequences give a regular language).
- Juris Hartmanis, "Computational complexity of one-tape Turing machine computations", Journal of the ACM 15(2), 325–339, 1968 (deterministic time $o(n\log n)$ gives only regular languages).
- B. A. Trakhtenbrot, "Turing computations with logarithmic delay", Algebra i Logika 3(4), 33–48, 1964.
- Kojiro Kobayashi, "On the structure of one-tape nondeterministic Turing machine time hierarchy", Theoretical Computer Science 40(2–3), 175–193, 1985, Theorem 3.3 (time $o(n\log n)$ forces bounded crossing sequences).
- Kohtaro Tadaki, Tomoyuki Yamakami and Jack C. H. Lin, "Theory of one-tape linear-time Turing machines", Theoretical Computer Science 411(1), 22–43, 2010, Proposition 3.1 and Lemmas 4.2–4.3.
