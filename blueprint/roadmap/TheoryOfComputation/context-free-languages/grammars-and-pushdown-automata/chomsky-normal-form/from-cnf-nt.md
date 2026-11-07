# Decoding basic nonterminals of the binarized grammar

Let $G$ be a context-free
grammar with nonterminals $N$ and initial nonterminal $S$, and let $t_0, \dots, t_{k-1}$ be
the list of terminals occurring in the production outputs of $G$. This map sends an element of
$N \sqcup \mathbb{N}$ (a basic nonterminal of the binarized grammar) to a symbol of $G$: a
nonterminal $A \in N$ goes to $A$, an index $i < k$ goes to the terminal $t_i$, and an index
$i \ge k$ goes to the nonterminal $S$.

Indices $i \ge k$ never arise from encoding nonterminals of $G$ or terminals occurring in the
production outputs of $G$.
