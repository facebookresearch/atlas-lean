# Nondeterministic Turing machines

The single-tape nondeterministic Turing machines of this topic are nondeterministic automata over
transition labels: a label reads a symbol (the run continues only if the cell under the head holds
that symbol), writes a symbol, moves the head one cell left or right, or does nothing. No label can
test for a blank cell or write a blank. A machine accepts a word when some run from one of its
start states, on the tape holding the word with the head on its first symbol and every other cell
blank, reaches an accepting state. Acceptance by such machines is recursively enumerable, so a
deterministic single-tape machine recognizes it (M. Sipser, *Introduction to the Theory of
Computation*, Theorem 3.16). Because a run cannot
detect the end of its input, a machine that accepts a word also accepts every extension of it on
the right; in particular the decidable predicate $n = 0$ is recognized by no such machine.

## Single Tape NTM

- [Acceptance as a label list](accepts-iff-exists-labels.md)
- [Acceptance is closed under extension on the right](accepts-append.md)
- [An NTM that accepts the empty word accepts every word](accepts-of-accepts-nil.md)
- [No NTM accepts exactly the binary code of $0$](not-forall-accepts-encode-nat-iff-eq-zer.md)
- [Acceptance by a single-tape nondeterministic machine is recursively enumerable](re-pred-accepts.md)

## Decidability

- [Deterministic machines recognize NTM acceptance](single-tape-recognizable-accepts.md)
- [Deterministic machines recognize NTM acceptance along a computable map](single-tape-recognizable-accepts-comp.md)
- [Predicates recognizable by a single-tape nondeterministic machine](single-tape-ntmrecognizable.md)
- [A predicate recognized by a single-tape NTM is recognized by a deterministic single-tape machine](single-tape-recognizable.md)
- [No single-tape NTM recognizes $n = 0$](not-single-tape-ntmrecognizable-eq-zero.md)
- [A decidable predicate that no single-tape NTM recognizes](exists-single-tape-decidable-not-single.md)
