# Edit distance from one language to another

The edit distance from a language $L_1$ to a language $L_2$ is the supremum over words of $L_1$ of the least number of letter insertions, deletions and substitutions turning the word into some word of $L_2$; it can be infinite and is not symmetric.

For words $w_1,w_2$ over a finite alphabet $\Sigma$, the *edit distance* $\mathrm{ed}(w_1,w_2)$ is the least $k$ such that $w_2$ is obtained from $w_1$ by a sequence of $k$ single-letter operations, each an insertion, a deletion or a substitution of one letter: the [edit distance with letter costs](../../../ComputerScience/string-algorithms/edit-distance-with-general-costs/general-cost-edit-distance.md) for unit insertion, deletion and substitution costs and cost $0$ for keeping a letter. For languages $L_1,L_2\subseteq\Sigma^*$, the edit distance *from* $L_1$ *to* $L_2$ is

$$
\mathrm{ed}(L_1,L_2)=\sup_{w_1\in L_1}\ \inf_{w_2\in L_2}\ \mathrm{ed}(w_1,w_2)\in\mathbb N\cup\{\infty\}.
$$

with the usual conventions $\sup\emptyset = 0$ and $\inf\emptyset = \infty$: thus $\mathrm{ed}(\emptyset, L_2) = 0$ for every $L_2$, and $\mathrm{ed}(L_1, \emptyset) = \infty$ for nonempty $L_1$.

**Automata.** The automata are those of Section 2.1 of the source. A *pushdown automaton* (PDA) $(\Sigma,\Gamma,Q,S,\delta,F)$ has finite sets $\Gamma$ of stack symbols and $Q$ of states, initial states $S\subseteq Q$, final states $F\subseteq Q$ and a finite transition relation $\delta\subseteq Q\times\Sigma\times(\Gamma\cup\{\bot\})\times Q\times\Gamma^*$; there are no $\varepsilon$-transitions. A run on $w=w[1]\cdots w[k]$ is a sequence of $k+1$ configurations in $Q\times\Gamma^*$ that starts in an initial state with empty stack and consumes exactly one letter per transition: from $(q,\varepsilon)$ a transition $(q,w[i],\bot,q',u')$ leads to $(q',u')$, and from $(q,ua)$ a transition $(q,w[i],a,q',u')$ leads to $(q',uu')$. The run is *accepting* if it ends in a final state with empty stack, and $L(A)$ is the set of words with an accepting run; in particular $\varepsilon\in L(A)$ iff some initial state is final. A PDA is a *deterministic pushdown automaton* (DPDA) if $\lvert S\rvert=1$ and $\delta$ is a function from $Q\times\Sigma\times(\Gamma\cup\{\bot\})$ to $Q\times\Gamma^*$. An NFA is a PDA whose transitions never push, and a DFA a deterministic one; their languages are those of [encoded DFA](../../decision-procedures/encoded-finite-automata/language.md) and [encoded NFA](../../decision-procedures/encoded-finite-automata/language-2.md). This model differs from the [pushdown automata](../grammars-and-pushdown-automata/pushdown-automata/pda.md) of the repository, which allow $\varepsilon$-transitions and accept by empty stack in any state; the problems below use the model of the source.

For classes $\mathcal C_1,\mathcal C_2$ among DFA, NFA, DPDA and PDA, all of them finite, the *threshold edit distance problem* $\mathrm{TED}(\mathcal C_1,\mathcal C_2)$ asks, given $A_1\in\mathcal C_1$, $A_2\in\mathcal C_2$ and an integer $k\ge0$, whether $\mathrm{ed}(L(A_1),L(A_2))\le k$; the *finite edit distance problem* $\mathrm{FED}(\mathcal C_1,\mathcal C_2)$ asks whether $\mathrm{ed}(L(A_1),L(A_2))<\infty$.

The edit distance between languages is not a metric: $\mathrm{ed}(\{a\}^*,\{a,b\}^*)=0$ while $\mathrm{ed}(\{a,b\}^*,\{a\}^*)=\infty$, since $\mathrm{ed}(b^n,\{a\}^*)=n$. With threshold $0$ the TED problem is inclusion. For finite automata, TED is PSPACE-complete; from pushdown to finite automata it is EXPTIME-complete.

## Depends on

- [Edit distance under general letter costs](../../../ComputerScience/string-algorithms/edit-distance-with-general-costs/general-cost-edit-distance.md)
- [Language of an encoded DFA](../../decision-procedures/encoded-finite-automata/language.md)
- [Language of an encoded NFA](../../decision-procedures/encoded-finite-automata/language-2.md)

## Proof depends on

None.

## Sources

- Krishnendu Chatterjee, Thomas A. Henzinger, Rasmus Ibsen-Jensen and Jan Otop, "Edit Distance for Pushdown Automata", *Logical Methods in Computer Science* 13(3), 2017, paper 23, doi:[10.23638/LMCS-13(3:23)2017](https://doi.org/10.23638/LMCS-13(3:23)2017); numbering of arXiv:1504.08259v4 ([arXiv](https://arxiv.org/abs/1504.08259v4)): Section 2.1 (finite automata and pushdown automata, their runs and acceptance), Section 2 (edit distance between words and between languages) and the definition of the TED, FED and computation problems in Section 2.2 (problem statement).
