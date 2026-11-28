# FOLLOW sets of nonterminals

Let $g$ be a context-free grammar with terminal alphabet $T$, nonterminals $N$ and start symbol $S$; a sentential form is a word $\alpha$ over $T \cup N$, and $\alpha \Rightarrow^* w$ means that $\alpha$ derives the terminal word $w \in T^*$. Write $\Rightarrow^*$ also for derivation of sentential forms.

The FOLLOW set of a nonterminal $A$ is the set of terminals that occur immediately after $A$ in some sentential form derived from the start symbol:

$$\mathrm{FOLLOW}(A) = \{\, a \in T : S \Rightarrow^* u\, A\, a\, v \text{ for some sentential forms } u, v \,\}.$$

It is defined through derivations, not as the result of a fixpoint computation. The end of input is not a member.

## Sources

- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
