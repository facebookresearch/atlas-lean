# Binary flattened tree grammars and regular separability

Two disjoint languages are regularly separable if some regular language contains the first and avoids the second; binary flattened
tree grammars are context-free grammars that generate the bracketed encodings of binary trees, a form of visibly pushdown language.

**Separability.** Languages $L_1, L_2 \subseteq \Sigma^*$ are *separable* if there is a regular language $R \subseteq \Sigma^*$ with $L_1 \subseteq R$ and
$L_2 \cap R = \emptyset$. The *separability problem* for a class of grammars asks, given two grammars $G_1, G_2$ of the class with
$L(G_1) \cap L(G_2) = \emptyset$, whether $L(G_1)$ and $L(G_2)$ are separable; for context-free grammars it is undecidable (Hunt; Szymanski).

**Binary flattened tree grammars.** A *binary flattened tree grammar* (BFG) over $\Sigma$ is a [context-free grammar](../grammars-and-pushdown-automata/context-free-languages.md)
whose terminals are $\Sigma \cup \{\langle, \rangle\}$, with an opening and a closing bracket, and every production of which has one of the forms

$$
N \to t, \qquad N \to \langle\,\rangle, \qquad N \to \langle N_1 N_2 \rangle ,
$$

with $t \in \Sigma$ and nonterminals $N, N_1, N_2$. A BFG generates the XML-style encodings of a regular language of trees whose inner nodes have
two children, and its language is a [visibly pushdown language](visibly-pushdown-automata.md) with $\langle$ as call and $\rangle$ as return
symbol.

## Depends on

- [Context-free languages](../grammars-and-pushdown-automata/context-free-languages.md)
- [Visibly pushdown automata and visibly pushdown languages](visibly-pushdown-automata.md)

## Proof depends on

None.

## Sources

- E. Kopczyński, "Invisible pushdown languages", in *Proceedings of the 31st Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2016)*, pp. 867–872, ACM, 2016, doi:10.1145/2933575.2933579; read in arXiv:1511.00289v1: Section 2 (context-free grammars, binary flattened tree grammars, the definition of separability and the problems CFG-SEPARABILITY and BFG-SEPARABILITY).
