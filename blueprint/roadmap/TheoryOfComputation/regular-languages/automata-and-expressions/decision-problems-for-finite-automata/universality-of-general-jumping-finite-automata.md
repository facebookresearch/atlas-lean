# Universality of general jumping finite automata is undecidable

A general jumping finite automaton reads its input discontinuously, deleting at each step a factor from anywhere in the word; no algorithm decides whether such an automaton accepts every word.

A *general jumping finite automaton* (GJFA) $M=(Q,\Sigma,R,s,F)$ has finitely many states, a start state $s$, final states $F$ and finitely many rules $(r,v,q)$ with $v\in\Sigma^*$. In one step, in state $r$, the automaton applies a rule $(r,v,q)$ by deleting an occurrence of the factor $v$ from any position of the remaining input and moves to $q$; the choices of rule and occurrence are nondeterministic, and a word is accepted if some computation ends in a final state with the empty word. Equivalently, $w\in L(M)$ iff $w=\varepsilon$ and $s\in F$, or $w$ is obtained from $\varepsilon$ by inserting, anywhere, the labels $v_d,v_{d-1},\dots,v_1$ of an accepting path $v_1,\dots,v_d$ in reverse order.

**Theorem (Vorel).** Given a GJFA $M$ over $\Sigma$, it is undecidable whether $L(M)=\Sigma^*$ (Theorem 5 of arXiv:1511.08642v1).

This answers a question of Meduna and Zemek. The class of GJFA languages is incomparable with the regular and the context-free languages, is not closed under the Boolean operations, and is contained in both the context-sensitive languages and NP.

## Depends on

- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Universality of context-free grammars is undecidable](../../../undecidable-problems/undecidable-problems-for-context-free-grammars/exists-not-tm2-decidable-univ.md)

## Expansion

The reduction is from universality of context-free grammars, for a grammar $G$ in Greibach normal form without the empty word, with rules $B_i\to u_i$, $u_i\in\Sigma_T\Sigma_N^*$. The GJFA $M_G$ works over $\Gamma=\Sigma_T\cup\Sigma_N\cup\{b_1,\dots,b_m\}$ with five states and rules labeled by the words $b_iu_i$, $A_ib_i$ and certain two-letter words; a derivation of $G$ is recorded by rewriting $A_i$ into $A_ib_iu_i$ rather than into $u_i$, keeping the nonterminals. Words of $\Gamma^*$ that do not encode such derivations are accepted by easy paths, and a word of the shape $x_1t\,x_2t\cdots x_nt$ can only be accepted through a path inserting $b_iu_i$ next to an unmatched $A_i$, which simulates a derivation of $x_1\cdots x_n$. Hence $L(M_G)=\Gamma^*$ iff $L(G)=\Sigma_T^+$, that is, iff $G$ generates every nonempty word; the source writes $\Sigma_T^*$, but $G$ never generates the empty word, and universality of context-free grammars on nonempty words is undecidable, the empty word being a separate decidable check. The reduction uses [Greibach normal form](../../../context-free-languages/grammars-and-pushdown-automata/greibach-normal-form/is-greibach-normal-form.md) for context-free grammars. A good expansion links pages for the correctness of the construction of $M_G$ and for the conversion of a grammar without the empty word into Greibach normal form.

## Sources

- Vojtěch Vorel, "Two Results on Discontinuous Input Processing", in *Descriptional Complexity of Formal Systems (DCFS 2016)*, Lecture Notes in Computer Science 9777, 2016, pp. 205–216, doi:[10.1007/978-3-319-41114-9_16](https://doi.org/10.1007/978-3-319-41114-9_16); read in arXiv:1511.08642v1 ([arXiv](https://arxiv.org/abs/1511.08642v1)): the introduction, Section 2 (insertion and the characterization of GJFA languages) and Theorem 5 with its proof.
