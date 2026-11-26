# Quantum finite automata can be exponentially smaller than probabilistic ones

For a prime $p$ let $\mathrm{MOD}_p = \{a^j : p \text{ divides } j\}$. Every probabilistic finite automaton recognizing $\mathrm{MOD}_p$ with bounded error has at least $p$
states, while for every $\varepsilon > 0$ there is a Moore–Crutchfield [quantum finite automaton](one-way-quantum-finite-automata.md) with $O(\log p)$ states recognizing $\mathrm{MOD}_p$
with error at most $\varepsilon$ (Ambainis and Freivalds). The quantum automaton runs, in superposition, two-state rotating automata for
suitably chosen rotation angles $2\pi k/p$.

## Depends on

- [One-way quantum finite automata](one-way-quantum-finite-automata.md)

## Sources

- A. Ambainis and A. Yakaryılmaz, "Automata and quantum computing", in J.-É. Pin (ed.), *Handbook of Automata Theory*, EMS Press, 2021; arXiv:1507.01988: Section 4.2, Theorem 4.7 and the construction that follows it, crediting A. Ambainis and R. Freivalds (FOCS 1998).
