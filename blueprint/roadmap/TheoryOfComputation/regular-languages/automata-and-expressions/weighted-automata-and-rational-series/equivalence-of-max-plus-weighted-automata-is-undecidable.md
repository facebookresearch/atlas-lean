# Equivalence of max-plus weighted automata is undecidable

There is no algorithm that decides, given two [weighted automata](weighted-automata-over-a-semiring.md) over the max-plus semiring
$(\mathbb{N} \cup \{-\infty\}, \max, +, -\infty, 0)$, whether their behaviors are equal (Krob). More precisely, there are series
$r_1, r_2 : \Sigma^* \to \mathbb{N} \cup \{-\infty\}$ such that each of the sets of max-plus weighted automata $\mathcal{A}$ with $\|\mathcal{A}\| = r_1$,
with $\|\mathcal{A}\| \le r_1$, and with $r_2 \le \|\mathcal{A}\|$ is undecidable; the same holds over the min-plus semiring
$(\mathbb{N} \cup \{\infty\}, \min, +, \infty, 0)$. Krob reduced Hilbert's tenth problem; a simpler proof reduces the halting problem of two-counter machines.

## Depends on

- [Weighted automata over a semiring](weighted-automata-over-a-semiring.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Sources

- M. Droste and D. Kuske, "Weighted automata", in J.-É. Pin (ed.), *Handbook of Automata Theory*, vol. I, EMS Press, 2021, Chapter 4 (authors' version, <https://eiche.theoinf.tu-ilmenau.de/kuske/Publications/DroK21.pdf>): Theorem 8.6, the remarks after it, and its proof following Almagor, Boker and Kupferman.
