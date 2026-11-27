# Visibly pushdown register automata

A visibly pushdown register automaton reads tags paired with data values; its registers always hold distinct data values, and the tag alone decides whether it pushes a tag and a datum on its stack, pops, or leaves the stack unchanged.

Let $\mathbb D$ be an infinite set of data values. For $r\ge1$, an *$r$-register assignment* of the *SF discipline* is an injective map $\rho:\{1,\dots,r\}\to\mathbb D$: registers are always filled (F) and hold pairwise distinct values (single assignment, S).

An *$r$-register visibly pushdown automaton* ($r$-VPDRA(SF)) is a tuple $(Q,\Sigma_C,\Sigma_N,\Sigma_R,\Gamma,\delta)$ with a finite set $Q$ of states, disjoint finite sets $\Sigma_C,\Sigma_N,\Sigma_R$ of push, no-op and pop tags, a finite set $\Gamma$ of stack tags, and transitions $\delta=\delta_C\cup\delta_N\cup\delta_R$ with labels $l\in\{1,\dots,r\}\cup\{1^\bullet,\dots,r^\bullet\}$: $\delta_C\subseteq Q\times\Sigma_C\times L\times\Gamma\times\{1,\dots,r\}\times Q$, $\delta_N\subseteq Q\times\Sigma_N\times L\times Q$ and $\delta_R\subseteq Q\times\Sigma_R\times L\times\Gamma\times(\{1,\dots,r\}\cup\{\bullet\})\times Q$. Configurations are triples $(q,\rho,s)$ with a stack $s\in(\Gamma\times\mathbb D)^*$. There is an edge $(q_1,\rho_1,s_1)\xrightarrow{(t,d)}(q_2,\rho_2,s_2)$ when, for some $i$ and $l\in\{i,i^\bullet\}$, $\rho_2$ agrees with $\rho_1$ outside $i$, the datum $d$ read is the one held in register $i$ afterwards, $\rho_2(i)=\rho_1(i)$ if $l=i$ while $\rho_2(i)$ is a value not in the range of $\rho_1$ if $l=i^\bullet$, and either a push transition $(q_1,t,l,t',j,q_2)$ pushes $(t',\rho_2(j))$, a no-op transition $(q_1,t,l,q_2)$ keeps the stack, or a pop transition $(q_1,t,l,t',j,q_2)$ pops $(t',d')$ with $d'=\rho_2(j)$ if $j\le r$ and $d'$ outside the range of $\rho_2$ if $j=\bullet$.

The *bisimilarity problem* asks, given an automaton and two configurations, whether they are bisimilar in this labeled transition system, whose labels are pairs (tag, data value).

## Depends on

- [Visibly pushdown automata and visibly pushdown languages](../../context-free-languages/visibly-pushdown-languages/visibly-pushdown-automata.md)
- [Register automata on data words](register-automata-on-data-words.md)

## Proof depends on

None.

## Expansion

Without a stack, bisimilarity of register automata and of fresh-register automata is decidable under every register discipline the source considers (single or multiple assignment; filled, initially empty or erasable registers), with tight complexity bounds except for the SF discipline; adding a visibly pushdown stack already breaks decidability under SF, the most restrictive discipline.

## Sources

- Andrzej S. Murawski, Steven J. Ramsay and Nikos Tzevelekos, "Bisimilarity in fresh-register automata", *Logical Methods in Computer Science* 21(1), 2025, paper 13, doi:[10.46298/lmcs-21(1:13)2025](https://doi.org/10.46298/lmcs-21(1:13)2025); read in arXiv:2005.06411v5 ([arXiv](https://arxiv.org/abs/2005.06411v5)), cited by section: the introduction's classification of register disciplines and the section on visibly pushdown automata with single assignment and filled registers (definition of $r$-VPDRA(SF)).
