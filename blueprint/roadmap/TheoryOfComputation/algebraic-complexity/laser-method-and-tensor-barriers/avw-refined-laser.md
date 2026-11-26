# Alman–Vassilevska Williams: refined laser method and omega < 2.37286

In the laser method analysis of $\mathrm{CW}_q^{\otimes 32}$, allowing zeroed-out block triples to be partially kept via a refined accounting of ``holes'' (instead of discarding every block triple sharing a block with another surviving triple) increases the obtained value. This gives the bound $\omega < 2.37286$, and the refinement applies to every tensor amenable to the laser method.

## Proof sketch

In standard hashing, each block appearing in two surviving triples causes one triple to be discarded. The refined method keeps triples with holes and shows that a matrix multiplication tensor with a small fraction of entries zeroed out (a tensor with holes) can still be degenerated, via a random-shift argument, into a full matrix multiplication tensor of slightly smaller size, so the loss is negligible.

## Depends on

- [The laser method bound on omega from tensor values](laser-method-bound.md)
- [Alman–Vassilevska Williams 2020 bound on the square exponent](../matrix-multiplication-exponent/alman-vassilevska-williams2020-upper.md)

## Proof depends on

- [The laser method bound on omega from tensor values](laser-method-bound.md)
- [Alman–Vassilevska Williams 2020 bound on the square exponent](../matrix-multiplication-exponent/alman-vassilevska-williams2020-upper.md)

## Sources

- J. Alman, V. Vassilevska Williams, "A refined laser method and faster matrix multiplication", SODA (2021), arXiv:2010.05846.
