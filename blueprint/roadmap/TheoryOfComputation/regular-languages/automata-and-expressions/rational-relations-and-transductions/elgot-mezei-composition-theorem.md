# Elgot–Mezei composition theorem

Let $A$, $B$ and $C$ be alphabets and let $\tau : A^* \to B^*$ and $\tau' : B^* \to C^*$ be rational transductions, in the sense of
[rational relations and transducers](rational-relations-and-transducers.md). Then their composition $\tau' \circ \tau : A^* \to C^*$, mapping
$x$ to $\bigcup_{y \in \tau(x)} \tau'(y)$, is rational (Elgot and Mezei).

## Depends on

- [Rational relations and transducers](rational-relations-and-transducers.md)

## Proof depends on

- [Nivat's theorem](nivat-s-theorem.md)

## Sources

- J. Berstel, *Transductions and Context-Free Languages*, Teubner, 1979; electronic edition of Chapters I–IV, 2007, <http://www-igm.univ-mlv.fr/~berstel/LivreTransductions/LivreTransductions.pdf>: Theorem III.4.4 and its proof through Lemma III.4.5.
