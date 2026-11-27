# Tag systems emulate Turing machines

Every Turing machine with $m$ states over the alphabet $\{0, 1\}$, working on tapes with finitely many cells different from $0$, is emulated by a
[tag system](tag-systems-and-cyclic-tag-systems.md) with $10m$ symbols $L_k, L_{k0}, L_{k1}, R_k, R_{k0}, R_{k1}, R_{k*}, H_k, H_{k0}, H_{k1}$ ($k$ a state): a configuration whose tape
to the left and to the right of the head forms the binary numbers $T_L$ and $T_R$ (less significant digits nearer the head) is encoded by
a tape with a number of $L$ and $R$ symbols proportional to $T_L$ and $T_R$, and each step of the Turing machine is carried out by a
sequence of tag-system steps that halves, doubles and adjusts these numbers (Cocke; Minsky). Hence tag systems are capable of
universal computation; the construction extends to $p$ tape symbols with deletion number $p$.

## Depends on

- [Halting of a single-tape machine](../../computability/halting-problem-for-single-tape-turing-machines/tm0-halts-on.md)
- [Tag systems and cyclic tag systems](tag-systems-and-cyclic-tag-systems.md)

## Sources

- M. Cook, "Universality in elementary cellular automata", *Complex Systems* 15(1):1–40, 2004: Section 2.1, the emulation of a two-symbol Turing machine "following a proof of Cocke", with footnotes 3 and 4, and note 12, which credits the proof to J. Cocke, "Universality of tag systems with P = 2", *Journal of the ACM* 11 (1964), and to M. Minsky.
