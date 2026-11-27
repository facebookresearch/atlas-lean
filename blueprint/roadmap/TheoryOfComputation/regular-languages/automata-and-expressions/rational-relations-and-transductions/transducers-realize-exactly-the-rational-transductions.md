# Transducers realize exactly the rational transductions

A transduction $\tau : A^* \to B^*$ is rational if and only if it is realized by a transducer, in the sense of
[rational relations and transducers](rational-relations-and-transducers.md) (Elgot and Mezei). Moreover every rational transduction
is realized by a transducer whose transitions read at most one letter, $E \subseteq Q \times (A \cup \{1\}) \times B^* \times Q$.

## Depends on

- [Rational relations and transducers](rational-relations-and-transducers.md)

## Sources

- J. Berstel, *Transductions and Context-Free Languages*, Teubner, 1979; electronic edition of Chapters I–IV, 2007, <http://www-igm.univ-mlv.fr/~berstel/LivreTransductions/LivreTransductions.pdf>: Theorem III.6.1 with its proof, the remark after the definition of transducers crediting Elgot and Mezei (1965), and Corollary III.6.2.
