# Whether a context-free grammar is ambiguous is undecidable

There is an alphabet $T$,
with decidable equality and a primitive recursive encoding into $\mathbb{N}$, such that no
multi-stack machine decides (in the sense of TM2-decidability), for an encoded context-free
grammar $G$ over $T$, whether $G$ is ambiguous, that is, whether some word has two different
leftmost derivations from the start nonterminal of $G$.

$T$ is not required to be finite. This is Sipser's problem $\mathit{AMBIG}_{\mathit{CFG}}$.
