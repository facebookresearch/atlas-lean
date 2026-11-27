# Cyclic tag systems emulate tag systems

For every [tag system](tag-systems-and-cyclic-tag-systems.md) with deletion number $2$ and symbols numbered $1, \dots, k$ there is a cyclic tag system that emulates it: symbol $i$ is encoded
by the word of length $k$ over $\{Y, N\}$ whose only $Y$ is at position $i$, the tape and the $k$ appendants are encoded letterwise, and the
list of the cyclic tag system consists of the $k$ encoded appendants in order followed by $k$ empty appendants. Reading an encoded
symbol at the start of the list appends exactly the encoded appendant; reading one halfway through the list appends nothing, which
emulates the ignored second symbol. The emulation is read at the start of each pass through the list and stops when fewer than two encoded
symbols remain, when the tag system halts. Hence cyclic tag systems are universal.

## Depends on

- [Tag systems and cyclic tag systems](tag-systems-and-cyclic-tag-systems.md)

## Proof depends on

- [Tag systems emulate Turing machines](tag-systems-emulate-turing-machines.md)

## Sources

- M. Cook, "Universality in elementary cellular automata", *Complex Systems* 15(1):1–40, 2004: Section 2.2, the construction of a cyclic tag system from a tag system and the argument that follows it.
