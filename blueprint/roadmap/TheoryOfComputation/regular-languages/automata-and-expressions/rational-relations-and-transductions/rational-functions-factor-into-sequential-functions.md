# Rational functions factor into left and right sequential functions

A partial function $\alpha : A^* \to B^*$ with $\alpha(1) = 1$ is a rational function, in the sense of
[rational relations and transducers](rational-relations-and-transducers.md), if and only if $\alpha = \rho \circ \lambda$ for a
[left sequential function](sequential-and-subsequential-functions.md) $\lambda : A^* \to C^*$ and a right sequential function
$\rho : C^* \to B^*$ for some alphabet $C$; moreover $\lambda$ can be chosen total and length preserving (Elgot and Mezei). The input is read once
from left to right and the intermediate word once from right to left.

## Depends on

- [Rational relations and transducers](rational-relations-and-transducers.md)
- [Sequential and subsequential functions](sequential-and-subsequential-functions.md)

## Proof depends on

- [Elgot–Mezei composition theorem](elgot-mezei-composition-theorem.md)

## Sources

- J. Berstel, *Transductions and Context-Free Languages*, Teubner, 1979; electronic edition of Chapters I–IV, 2007, <http://www-igm.univ-mlv.fr/~berstel/LivreTransductions/LivreTransductions.pdf>: Theorem IV.5.2 (Elgot and Mezei, 1965) with its proof, and Theorem IV.5.1 (bimachines).
