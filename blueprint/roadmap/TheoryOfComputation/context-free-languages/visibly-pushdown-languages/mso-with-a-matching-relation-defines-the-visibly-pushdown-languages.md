# Monadic logic with a matching relation defines exactly the visibly pushdown languages

Over a pushdown alphabet $\tilde\Sigma$, view a word $w$ as the structure on its positions with unary predicates $Q_a$ for $a \in \Sigma$, the order $\le$ and the
*matching relation* $\mu$, where $\mu(i, j)$ holds when $w[i]$ is a call and $w[j]$ is its matching return. *MSO$_\mu$* is
[monadic second-order logic](../../omega-automata-and-games/logic-and-tree-automata/monadic-second-order-logic-over-words.md) over these structures:
$\varphi ::= Q_a(x) \mid x \in X \mid x \le y \mid \mu(x, y) \mid \neg\varphi \mid \varphi \vee \varphi \mid \exists x.\varphi \mid \exists X.\varphi$. A language over $\tilde\Sigma$ is a
[visibly pushdown language](visibly-pushdown-automata.md) if and only if it is defined by an MSO$_\mu$ sentence. The proof follows Büchi's theorem for
finite words, with the stack of the automaton handling $\mu$.

## Depends on

- [Visibly pushdown automata and visibly pushdown languages](visibly-pushdown-automata.md)
- [Monadic second-order logic over words](../../omega-automata-and-games/logic-and-tree-automata/monadic-second-order-logic-over-words.md)

## Proof depends on

- [Closure properties of visibly pushdown languages](closure-properties-of-visibly-pushdown-languages.md)

## Sources

- R. Alur and P. Madhusudan, "Visibly pushdown languages", *Proceedings of the 36th ACM STOC*, 2004; full version of August 2005, whose numbering is cited, <https://www.cis.upenn.edu/~alur/Stoc04.pdf>: Section 3, the definition of the matching relation, Definition 3 (MSO$_\mu$) and Theorem 4 with its proof.
