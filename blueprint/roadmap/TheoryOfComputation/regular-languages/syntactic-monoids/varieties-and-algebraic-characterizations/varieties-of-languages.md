# Varieties of languages

A *$*$-class of recognizable languages* $\mathcal{V}$ assigns to each finite alphabet $A$ a set $\mathcal{V}(A^*)$ of recognizable languages of $A^*$. It is a
*$*$-variety of languages* if, for all finite alphabets $A$ and $B$:
1. $\mathcal{V}(A^*)$ is a Boolean algebra of languages;
2. for every monoid morphism $\varphi : A^* \to B^*$, $L \in \mathcal{V}(B^*)$ implies $\varphi^{-1}(L) \in \mathcal{V}(A^*)$;
3. if $L \in \mathcal{V}(A^*)$ and $a \in A$, then the quotients $a^{-1} L = \{w : aw \in L\}$ and $L a^{-1} = \{w : wa \in L\}$ belong to $\mathcal{V}(A^*)$.

Dropping closure under complement in 1 gives *positive* $*$-varieties, and the same definitions over $A^+$ with semigroup morphisms give
$+$-varieties.

## Sources

- J.-É. Pin, "Syntactic semigroups", in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 1, Springer, 1997, pp. 679–746, author's copy <https://www.irif.fr/~jep/PDF/HandBook.pdf>: Section 4.2, the definitions of classes of recognizable languages, positive varieties and varieties, and of $*$-classes and $*$-varieties.
