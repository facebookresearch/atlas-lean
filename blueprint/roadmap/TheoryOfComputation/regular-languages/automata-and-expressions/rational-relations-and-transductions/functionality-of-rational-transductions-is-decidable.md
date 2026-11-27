# Functionality of rational transductions is decidable

Given a transducer, in the sense of [rational relations and transducers](rational-relations-and-transducers.md), one can decide whether the
transduction it realizes is a rational function, that is, maps every input word to at most one output word. For a normalized matrix
representation with $m$ states it suffices to check that every input word of length at most $1 + 2m(m - 1)$ has at most one output between
every pair of states.

## Depends on

- [Rational relations and transducers](rational-relations-and-transducers.md)

## Sources

- J. Berstel, *Transductions and Context-Free Languages*, Teubner, 1979; electronic edition of Chapters I–IV, 2007, <http://www-igm.univ-mlv.fr/~berstel/LivreTransductions/LivreTransductions.pdf>: Proposition IV.1.1 and Theorem IV.1.2 with its proof.
