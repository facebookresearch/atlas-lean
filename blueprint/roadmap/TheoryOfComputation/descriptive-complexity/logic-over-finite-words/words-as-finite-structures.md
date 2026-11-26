# Words as finite structures; FO[<] and MSO definability

Over a finite alphabet $\Sigma$, a word $w = a_1 \cdots a_\ell$ is the structure with universe $\{1,\dots,\ell\}$, the order $<$ and unary predicates $P_a = \{i : a_i = a\}$ for $a \in \Sigma$ (the empty word is the empty structure). A language $L \subseteq \Sigma^*$ is *FO[<]-definable* if some first-order sentence over $\{<\} \cup \{P_a\}$ holds exactly in the words of $L$, and *MSO-definable* if some monadic second-order sentence (with quantification over sets of positions) does.

## Depends on

- [Monadic second-order logic over words](../../omega-automata-and-games/logic-and-tree-automata/monadic-second-order-logic-over-words.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- W. Thomas, "Languages, Automata, and Logic", in Handbook of Formal Languages, Vol. 3, Springer, 389–455, 1997.
