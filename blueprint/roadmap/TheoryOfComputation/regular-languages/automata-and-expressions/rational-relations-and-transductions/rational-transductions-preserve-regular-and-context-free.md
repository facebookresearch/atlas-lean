# Rational transductions preserve regular and context-free languages

Let $\tau : A^* \to B^*$ be a rational transduction, in the sense of [rational relations and transducers](rational-relations-and-transducers.md),
and for $X \subseteq A^*$ let $\tau(X) = \bigcup_{x \in X} \tau(x)$. If $X$ is regular then $\tau(X)$ is regular, and if $X$ is context-free then
$\tau(X)$ is context-free. In particular the domain and the image of a rational transduction are regular languages.

## Depends on

- [Rational relations and transducers](rational-relations-and-transducers.md)
- [Language generated from a nonterminal](../../../context-free-languages/grammars-and-pushdown-automata/context-free-grammars/language-from.md)

## Proof depends on

- [Nivat's theorem](nivat-s-theorem.md)

## Sources

- J. Berstel, *Transductions and Context-Free Languages*, Teubner, 1979; electronic edition of Chapters I–IV, 2007, <http://www-igm.univ-mlv.fr/~berstel/LivreTransductions/LivreTransductions.pdf>: Corollary III.4.2, and the remark in Section III.4 that the domain and image are regular.
