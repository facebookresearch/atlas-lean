# Equivalence of rational functions is decidable

Given two rational functions $\alpha, \beta : A^* \to B^*$ by transducers, in the sense of
[rational relations and transducers](rational-relations-and-transducers.md), one can decide whether $\alpha \subseteq \beta$, that is,
$\beta$ extends $\alpha$, and whether $\alpha = \beta$. Indeed $\alpha \subseteq \beta$ holds exactly when $\mathrm{dom}(\alpha) \subseteq \mathrm{dom}(\beta)$ and the union
$\alpha \cup \beta$ is a function. This contrasts with the undecidability of equivalence for rational relations in general.

## Depends on

- [Rational relations and transducers](rational-relations-and-transducers.md)

## Proof depends on

- [Functionality of rational transductions is decidable](functionality-of-rational-transductions-is-decidable.md)
- [Rational transductions preserve regular and context-free languages](rational-transductions-preserve-regular-and-context-free.md)

## Sources

- J. Berstel, *Transductions and Context-Free Languages*, Teubner, 1979; electronic edition of Chapters I–IV, 2007, <http://www-igm.univ-mlv.fr/~berstel/LivreTransductions/LivreTransductions.pdf>: Corollary IV.1.3 and its proof.
