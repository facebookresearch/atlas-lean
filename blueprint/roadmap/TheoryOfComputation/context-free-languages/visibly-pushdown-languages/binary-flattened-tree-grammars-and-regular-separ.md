# Binary flattened tree grammars

Binary flattened tree grammars are context-free grammars that generate the bracketed encodings of regular sets of binary trees, a form
of visibly pushdown language.

A *binary flattened tree grammar* (BFG) over $\Sigma$ is a [context-free grammar](../grammars-and-pushdown-automata/context-free-languages.md)
whose terminals are $\Sigma \cup \{\langle, \rangle\}$, with an opening bracket $\langle$ and a closing bracket $\rangle$ that are distinct and do not belong to $\Sigma$, and every production of which has one of the forms

$$
N \to t, \qquad N \to \langle\,\rangle, \qquad N \to \langle N_1 N_2 \rangle ,
$$

with $t \in \Sigma$ and nonterminals $N, N_1, N_2$. A BFG generates the XML-style encodings of a [regular language of trees](../../omega-automata-and-games/logic-and-tree-automata/bottom-up-finite-tree-automata.md) whose inner nodes have
two children, and its language is a [visibly pushdown language](visibly-pushdown-automata.md) with $\langle$ as call and $\rangle$ as return
symbol.

## Depends on

- [Context-free languages](../grammars-and-pushdown-automata/context-free-languages.md)
- [Visibly pushdown automata and visibly pushdown languages](visibly-pushdown-automata.md)
- [Bottom-up finite tree automata](../../omega-automata-and-games/logic-and-tree-automata/bottom-up-finite-tree-automata.md)


## Proof depends on

None.

## Sources

- E. Kopczyński, "Invisible pushdown languages", in *Proceedings of the 31st Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2016)*, pp. 867–872, ACM, 2016, doi:10.1145/2933575.2933579; read in arXiv:1511.00289v1: Section 2 (context-free grammars and binary flattened tree grammars).
