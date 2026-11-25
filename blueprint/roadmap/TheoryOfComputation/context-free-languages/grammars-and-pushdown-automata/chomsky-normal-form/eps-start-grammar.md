# Grammar with a fresh nullable start symbol

Given a context-free grammar $G$ with
nonterminals $N$ and initial nonterminal $S$, this is the grammar with nonterminals
$N \cup \{S_0\}$ for a fresh symbol $S_0$, initial nonterminal $S_0$, and the following
productions: every production of $G$; the empty production $S_0 \to \varepsilon$; and
$S_0 \to \alpha$ for every production $S \to \alpha$ of $G$.

The new grammar generates the language of $G$ plus the empty word, and stays in Chomsky normal
form when $G$ is in Chomsky normal form and has no empty outputs.
