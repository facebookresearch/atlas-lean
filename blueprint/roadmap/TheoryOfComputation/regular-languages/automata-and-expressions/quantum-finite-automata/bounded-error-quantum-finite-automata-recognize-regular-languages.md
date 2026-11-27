# Bounded-error quantum finite automata recognize only regular languages

Fix $\varepsilon < 1/2$. If a language is recognized with error at most $\varepsilon$ by an $n$-state [one-way quantum finite automaton](one-way-quantum-finite-automata.md) with pure states, such as a
Moore–Crutchfield or Kondacs–Watrous automaton, then it is recognized by a deterministic finite automaton with $2^{O(n)}$ states; for automata
with mixed states the bound is $2^{O(n^2)}$ states, the constants depending on $\varepsilon$ (the cited proofs take error at most $1/3$). Without a fixed
$\varepsilon$ no bound in $n$ holds: the two-state rotation by $2\pi/p$, accepting the lengths $j$ with $\cos^2(2\pi j/p) > 1/2$, needs a deterministic automaton with $p$
states for every odd prime $p \ge 5$. In particular these models recognize only regular languages with bounded error, and
they are not all equal in power: Moore–Crutchfield automata recognize with bounded error exactly the group languages (those whose syntactic
monoid is a group), and Kondacs–Watrous automata cannot recognize the regular language $\{a, b\}^* a$.

## Depends on

- [One-way quantum finite automata](one-way-quantum-finite-automata.md)

## Sources

- A. Ambainis and A. Yakaryılmaz, "Automata and quantum computing", in J.-É. Pin (ed.), *Handbook of Automata Theory*, EMS Press, 2021; arXiv:1507.01988: Section 4.1, Theorem 4.4 (pure states, crediting A. Kondacs and J. Watrous and A. Ambainis and R. Freivalds) and Theorem 4.6 (mixed states) with their proofs, and Section 4.3, the paragraphs on the classes recognized with bounded error (group languages for Moore–Crutchfield automata; $\{a,b\}^*a$ for Kondacs–Watrous automata).
