# Languages of rank-$n$ types are star-free

Over a finite alphabet, for every $n$ and every rank-$n$ type $\tau$ of words, the language of words of type $\tau$ is star-free (it lies in the smallest family of languages containing $\Sigma^*$ and the singletons $\{a\}$, $a \in \Sigma$, closed under finite union, complement in $\Sigma^*$ and concatenation); so is the language of pointed words whose split at the pointed position has prescribed types on the left and right. Since every FO[<] sentence of quantifier rank $n$ defines a finite union of such type languages, every FO[<]-definable language is star-free (the hard direction of McNaughton–Papert).

## Proof sketch

Induction on $n$: the rank-$(n+1)$ type of a word is determined by which pairs (type of prefix, letter, type of suffix) occur at positions, and the set of words realizing or avoiding such a split is a Boolean combination of concatenations of rank-$n$ type languages with single letters, by EF composition.

## Depends on

- [Words as finite structures; FO[<] and MSO definability](words-as-finite-structures.md)

## Proof depends on

- [EF games compose over concatenations of words](ef-games-compose-over-concatenation.md)
- [Finitely many formulas of bounded quantifier rank up to equivalence](../finite-structures-and-definability/finitely-many-formulas-of-bounded-rank.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- R. McNaughton and S. Papert, Counter-Free Automata, MIT Press, 1971.
- W. Thomas, "Languages, Automata, and Logic", in Handbook of Formal Languages, Vol. 3, Springer, 389–455, 1997.
