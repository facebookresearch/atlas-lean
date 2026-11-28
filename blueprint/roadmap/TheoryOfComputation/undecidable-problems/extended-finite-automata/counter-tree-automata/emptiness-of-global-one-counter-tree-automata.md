# Emptiness of global one-counter tree automata is undecidable

A global one-counter tree automaton reads a ranked tree top-down, node after node in a fixed order, with a single nonnegative counter shared across the whole tree; no algorithm decides whether it accepts any tree, although membership of a given tree is decidable in polynomial time.

A *global one-counter tree automaton* (GOCTA) $\mathcal A=(Q,\Sigma,q_0,\Delta)$ over a ranked alphabet $\Sigma$ has finitely many states, an initial state $q_0$, and transitions of the forms $q\xrightarrow{p/z}q'$ ($\varepsilon$-transitions) and $q\xrightarrow{p/z}\sigma(q_1,\dots,q_n)$ (read transitions), where $p\in\{0,{>}0,\top\}$ is a test on the counter and $z\in\mathbb Z$ an update keeping the counter nonnegative. Starting from $q_0$ with counter $0$, the automaton expands the tree top-down, always applying a transition at the lexicographically first position still carrying a state; the single counter is *global*, i.e. it is carried along this traversal across all branches. A tree is accepted if some computation produces it; finite tree automata are the special case without counter tests and updates.

**Theorem (Herrmann and Mörbitz).** Given a GOCTA $\mathcal A$, it is undecidable whether $L(\mathcal A)=\emptyset$ (Theorem 1 of arXiv:2406.15090v1).

In contrast, the uniform membership problem for GOCTA, whether a given tree is accepted by a given automaton, is decidable in polynomial time, using a polynomial bound on the counter values in computations. The source also shows that global index grammars (Castaño), a related formalism with a global pushdown, can generate non-semilinear languages, refuting the claim that they generate only semilinear languages and casting doubt on the claimed decidability of their emptiness, which it conjectures to be undecidable.

## Depends on

- [Bottom-up finite tree automata](../../../omega-automata-and-games/logic-and-tree-automata/bottom-up-finite-tree-automata.md)
- [Top-down tree automata](../../../omega-automata-and-games/logic-and-tree-automata/top-down-tree-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The source reduces emptiness of indexed counter grammars with a global counter semantics (R-mode derivations of Duske, Middendorf and Parchmann), which are Turing-complete: given such a grammar, a GOCTA recognizes its computation trees. The underlying reason is that a global counter can multiply its value by a constant, so it can simulate a pushdown storage by representing each pushdown content as a number in base $m$, and a context-free grammar with a global pushdown is Turing-complete. A good expansion links the Turing-completeness of indexed counter grammars with global counter semantics.

## Sources

- Luisa Herrmann and Richard Mörbitz, "Global one-counter tree automata", *Theoretical Computer Science* 1071, 2026, article 115840, doi:[10.1016/j.tcs.2026.115840](https://doi.org/10.1016/j.tcs.2026.115840); read in arXiv:2406.15090v1 ([arXiv](https://arxiv.org/abs/2406.15090v1)), whose numbering is used: Section 3 (the automaton model and examples), Theorem 1, Conjecture 1 and Theorem 2 in Section 5, and Lemma 8 in the appendix (the reduction from indexed counter grammars).
