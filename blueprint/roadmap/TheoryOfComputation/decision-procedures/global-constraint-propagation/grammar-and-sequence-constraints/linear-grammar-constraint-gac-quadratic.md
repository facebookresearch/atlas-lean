# Generalized arc consistency of GRAMMAR for linear grammars in quadratic time

For a linear context-free grammar, one with at most one nonterminal on every right-hand side, the CYK-based domain consistency propagator of the GRAMMAR constraint runs in $O(n^2|G|)$ time, matching the quadratic membership test for linear languages.

A context-free grammar without empty productions is **linear** when every production has at most one nonterminal on its right-hand side. Linear languages strictly contain the regular languages and are strictly contained in the context-free languages. Let $|G|=\sum_{A\to\alpha}|A\alpha|$ and consider $\mathrm{GRAMMAR}(G,[X_1,\dots,X_n])$ as on the [GRAMMAR and REGULAR constraints](grammar-constraint.md) page.

**Theorem.** If $G$ is linear and $n\ge1$, there is a propagator enforcing [generalized arc consistency](../generalized-arc-consistency.md) on $\mathrm{GRAMMAR}(G,[X_1,\dots,X_n])$ in $O(n^2|G|)$ time, counting table operations with constant-time tests of whether a terminal lies in a domain (reading and writing the domains adds $O(\sum_i|D(X_i)|)$).

## Depends on

- [GRAMMAR and REGULAR constraints](grammar-constraint.md): the constraint and the grammar size.
- [Generalized arc consistency](../generalized-arc-consistency.md): the consistency enforced.

## Proof depends on

None.

## Expansion

In $O(|G|)$ time put $G$ in the form $A\to aB$, $A\to Ba$, $A\to a$ (the source cites Theorem 12.3 of Wagner and Wechsung's *Computational Complexity* for this normal form of linear grammars and describes the splitting of long productions), then replace each terminal $a$ occurring beside a nonterminal by a new nonterminal $Y_a$ with $Y_a\to a$, which yields Chomsky normal form without enlarging the CYK table beyond its diagonal entries for the $Y_a$. The propagator is the monolithic CYK-based propagator of Quimper–Walsh (CP 2006) and Sellmann (CP 2006), whose domain consistency the source takes from those papers: a bottom-up table of nonterminals over the domains, then a top-down marking from $S$ that keeps only entries on a parse of the whole sequence and prunes the unmarked terminals. It builds a table of $O(n^2|N|)$ entries and then marks the entries reachable from $S$; its cost is the number of one-step expansions of table entries. For an arbitrary grammar an entry $A\in V[i,j]$ can be expanded in $O(nF(A))$ ways ($F(A)$ the number of productions with left side $A$, one per split point), giving $O(n^3|G|)$; for a linear grammar one side of every binary production generates a single symbol, so there is only one split point per production and $O(F(A))$ expansions, giving $n^2\sum_A F(A)=O(n^2|G|)$.

The source extends the bound to weighted linear grammars and observes that "fixed-growth" grammars, a subclass containing the regular grammars, allow linear-time propagation.

## Sources

- G. Katsirelos, S. Maneth, N. Narodytska and T. Walsh, "Restricted global grammar constraints", *Principles and Practice of Constraint Programming – CP 2009*, Lecture Notes in Computer Science 5732 (2009), 501–508, doi:10.1007/978-3-642-04244-7_40. Linear grammars and Theorem 3 with its proof, §4 of arXiv:0906.5233v1, [https://arxiv.org/abs/0906.5233v1](https://arxiv.org/abs/0906.5233v1).
