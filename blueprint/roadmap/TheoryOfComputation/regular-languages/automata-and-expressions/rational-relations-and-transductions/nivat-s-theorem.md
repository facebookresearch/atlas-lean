# Nivat's theorem

Let $A$ and $B$ be alphabets. For a transduction $\tau : A^* \to B^*$ the following are equivalent, in the sense of
[rational relations and transducers](rational-relations-and-transducers.md):

1. $\tau$ is rational;
2. there are an alphabet $C$, morphisms $\varphi : C^* \to A^*$ and $\psi : C^* \to B^*$ and a regular language $K \subseteq C^*$ such that
   $\tau(x) = \psi(\varphi^{-1}(x) \cap K)$ for every $x \in A^*$;
3. the same with $\varphi$ and $\psi$ alphabetic, that is, mapping each letter to a letter or to the empty word.

Equivalently, a relation $X \subseteq A^* \times B^*$ is rational if and only if $X = \{(\varphi z, \psi z) : z \in K\}$ for such $C$, $\varphi$, $\psi$ and $K$
(Nivat).

## Depends on

- [Rational relations and transducers](rational-relations-and-transducers.md)

## Sources

- J. Berstel, *Transductions and Context-Free Languages*, Teubner, 1979; electronic edition of Chapters I–IV, 2007, <http://www-igm.univ-mlv.fr/~berstel/LivreTransductions/LivreTransductions.pdf>: Theorem III.3.2 (rational relations) and Theorem III.4.1 (rational transductions), both credited to Nivat (1968).
