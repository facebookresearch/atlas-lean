# Emptiness of ∀*- and ∃∀-context-free hypergrammars is undecidable

No algorithm decides whether a context-free hypergrammar whose quantification condition consists of universal quantifiers only, or of one existential followed by one universal quantifier, derives some nonempty language.

**Theorem.** The emptiness problem is undecidable for $\forall^*$-[context-free hypergrammars](context-free-hypergrammars-and-hyperlanguages.md) and for $\exists\forall$-context-free hypergrammars: there is no algorithm that decides, given such a hypergrammar $G$, whether $\mathcal{H}(G) = \emptyset$.

With a single quantifier $\forall x$ the problem reduces to emptiness of a context-free grammar and is in polynomial time, as it is for $\exists^*$-CFHG. The proof reduces the Post correspondence problem to a hypergrammar with quantification condition $\forall x_1 \forall x_2$ (and to one with $\exists x_1 \forall x_2$), so emptiness is already undecidable for these two prefixes. The underlying grammar in the proof is linear, so the result also applies to asynchronous hyperautomata.

## Proof sketch

Let $[a_1, b_1], \dots, [a_n, b_n]$ be an instance of the Post correspondence problem over $\{a, b\}$. Pad the shorter of $a_i, b_i$ with $\#$ to obtain words $A_i, B_i$ of equal length, and let $G$ have variables $x_1, x_2$, condition $\forall x_1 \forall x_2$ and the single nonterminal $V_0$ with productions $V_0 \to \{A_{i, x_1}, B_{i, x_2}\} V_0 \mid \{A_{i, x_1}, B_{i, x_2}\}$ for $1 \le i \le n$, where $\{A_{i, x_1}, B_{i, x_2}\}$ is the word assignment of $A_i$ to $x_1$ and $B_i$ to $x_2$. If $\mathcal{L} \in \mathcal{H}(G)$ and $u \in \mathcal{L}$, the $\forall\forall$ condition applied with $u$ for both variables yields a derivation whose two components, with padding removed, both equal $u$, so $u = a_{i_1} \cdots a_{i_m} = b_{i_1} \cdots b_{i_m}$ is a solution; conversely, a solution $u$ gives $\{u\} \in \mathcal{H}(G)$. For $\exists\forall$ the same grammar works, since the universal quantifier must also range over the word chosen for the existential one.

## Depends on

- [Context-free hypergrammars and hyperlanguages](context-free-hypergrammars-and-hyperlanguages.md)
- [Context-free languages](../grammars-and-pushdown-automata/context-free-languages.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Sources

- H. Frenkel and S. Sheinvald, "Realizable and Context-Free Hyperlanguages", in P. Ganty and D. Della Monica (eds.), *Proceedings of the 13th International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2022)*, Electronic Proceedings in Theoretical Computer Science 370, 2022, pp. 114–130, doi:[10.4204/EPTCS.370.8](https://doi.org/10.4204/EPTCS.370.8); numbering of arXiv:2209.10306v1: Theorem 18 with its proof and the remarks after it, in Section 4.
