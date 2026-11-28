# Backward propagation decides path feasibility

Path feasibility of a loop-free string program is decidable whenever every assertion is a recognisable relation and every operation pulls regular languages back to recognisable relations, effectively from their descriptions: regular constraints can then be propagated backwards onto the inputs, one assignment at a time.

Let $\Sigma$ be a finite alphabet. A *symbolic execution* is a program

$$
S ::= y := f(x_1, \dots, x_r) \mid \mathrm{assert}(g(x_1, \dots, x_r)) \mid S; S
$$

in single static assignment form (each variable assigned at most once, and only after the variables it uses; arguments need not be distinct), where $f : (\Sigma^*)^r \to 2^{\Sigma^*}$ is a nondeterministic partial string function, with graph $R_f \subseteq (\Sigma^*)^r \times \Sigma^*$, and $g \subseteq (\Sigma^*)^r$ is a string relation, both taken from classes of operations and relations with finite descriptions. Variables never assigned are *inputs*. $S$ is *path-feasible* if some words for the inputs, and for each assignment $y := f(\vec x)$ a value $y \in f(\vec x)$ (which requires $f(\vec x) \neq \emptyset$), make every assertion true.

An $r$-ary relation $R \subseteq (\Sigma^*)^r$ is *recognisable* if it is a finite union $\bigcup_{i=1}^n L^{(i)}_1 \times \dots \times L^{(i)}_r$ of products of regular languages; a *representation* lists nondeterministic finite automata for the $L^{(i)}_j$. The *pre-image* of $L \subseteq \Sigma^*$ under $f$ is $\mathrm{Pre}_{R_f}(L) = \{\vec w : \exists w \in f(\vec w),\ w \in L\}$. Consider the conditions

- (RegMonDec) every assertion $g$ in $S$ is a recognisable relation, and a representation of it is computable from its description;
- (RegInvRel) for every operation $f$ in $S$ and every automaton $A$, $\mathrm{Pre}_{R_f}(L(A))$ is a recognisable relation, and a representation of it is computable from $A$ and the description of $f$.

If $S$ satisfies RegMonDec and RegInvRel, then path feasibility of $S$ is decidable.

## Depends on

None.

## Proof depends on

- [Emptiness of NFAs is decidable](../encoded-finite-automata/tm2-decidable-language-eq-zero.md)

## Expansion

This node still needs its proof broken down into the effective elimination step and its correctness. Remove the last assignment $y := f(\vec x)$. Each assertion mentioning $y$ is recognisable: guess one of its disjuncts and split it into membership assertions on its arguments (an argument occurring twice receives both memberships). Intersect, by the product construction, the automata now constraining $y$ into one automaton $A$; if there are none, take $A$ accepting $\Sigma^*$, so that the step still enforces that $f(\vec x)$ is defined. Intersection must come before the pre-image, since for a relation $\mathrm{Pre}_{R_f}(L_1 \cap L_2)$ may differ from $\mathrm{Pre}_{R_f}(L_1) \cap \mathrm{Pre}_{R_f}(L_2)$. Delete the assignment and those assertions and add $\mathrm{assert}(\mathrm{Pre}_{R_f}(L(A))(\vec x))$, recognisable by RegInvRel. The program is feasible iff some choice of disjuncts yields a feasible program, and the number of assignments drops by one. When none remain, split the remaining multivariate assertions on inputs into memberships by guessing disjuncts and test each input's intersection of automata for nonemptiness.

Examples from the source: concatenation satisfies RegInvRel, since $\mathrm{Pre}_{\circ}(L(A)) = \bigcup_q L(A_{q_0, q}) \times L(A_{q, F})$ over the states $q$ of $A$; finite-state and two-way transductions, string reversal and the [leftmost-longest replaceAll](leftmost-longest-replaceall.md) with a regular pattern not matching the empty word (with recognisable pre-images shown in the 2018 replaceAll paper) satisfy it too ([two-way transducers keep path feasibility decidable](two-way-transducers-keep-path-feasibility-decidable.md)). Unary-to-binary conversion does not: the pre-image of $10^*$ is $\{1^{2^j}\}$, which is not regular. The conditions are sufficient, not necessary: $|x_1| = |x_2|$ is not recognisable, yet some fragments with length constraints [remain decidable](expspace-fragments-with-replaceall-reverse-and-transducers.md).

## Sources

- T. Chen, M. Hague, A. W. Lin, P. Rümmer and Z. Wu, "Decision procedures for path feasibility of string-manipulating programs with complex operations", Proceedings of the ACM on Programming Languages 3 (POPL), Article 49, 2019, doi:[10.1145/3290362](https://doi.org/10.1145/3290362); full version arXiv:1811.03167v1, <https://arxiv.org/abs/1811.03167v1>: Section 3, the grammar (3) and footnote 4 (SSA form), Definition 3.1, Examples 3.2–3.4, the conditions RegMonDec and RegInvRel, Theorem 3.5 with its proof, Example 3.6, Remark 3.7, Example 5.2 (pre-images of relations do not distribute over intersection), Proposition 4.6, and the remark after Theorem 5.9.
