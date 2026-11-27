# Even length is MSO-definable but not FO[<]-definable

Over every nonempty finite alphabet, the language of words of even length is regular and MSO-definable (guess the set of odd positions), but it is not FO[<]-definable. Hence $\mathrm{FO}[<] \subsetneq \mathrm{MSO}$ on finite words: there is a regular language that is not first-order definable. Over a one-letter alphabet $\{a\}$ the language is $(aa)^*$, which is therefore not star-free.

## Proof sketch

A first-order sentence about words over $\{a\}$ is a sentence about finite linear orders, whose definable classes are finite or cofinite, so EVEN is not definable; for larger alphabets restrict to words over one letter (Straubing and Weil state the case of an arbitrary alphabet as a consequence of their characterization of the first-order definable languages). Not star-free follows because star-free languages are first-order definable.

## Depends on

- [Words as finite structures; FO[<] and MSO definability](words-as-finite-structures.md)
- [Kleene's theorem](../../regular-languages/automata-and-expressions/kleene-s-theorem/is-regular-iff-exists-regex.md)

## Proof depends on

- [First-order definable classes of finite linear orders are finite or cofinite](../ehrenfeucht-fraisse-games/even-not-definable-on-linear-orders.md)
- [Büchi–Elgot–Trakhtenbrot theorem](../../omega-automata-and-games/logic-and-tree-automata/buchielgottrakhtenbrot-theorem.md)
- [First-order definable word languages are exactly the star-free languages](../../regular-languages/first-order-definable-languages-are-star-free.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- H. Straubing and P. Weil, "An Introduction to Finite Automata and Their Connection to Logic", in D. D'Souza and P. Shankar (eds.), Modern Applications of Automata Theory, World Scientific, 2012; arXiv:1011.6491, Example 1.15 (over an arbitrary alphabet $A$, the MSO sentence defining the words of even length, and that this language cannot be described by a first-order formula).
- R. McNaughton and S. Papert, Counter-Free Automata, MIT Press, 1971.
- W. Thomas, "Languages, Automata, and Logic", in Handbook of Formal Languages, Vol. 3, Springer, 389–455, 1997.
