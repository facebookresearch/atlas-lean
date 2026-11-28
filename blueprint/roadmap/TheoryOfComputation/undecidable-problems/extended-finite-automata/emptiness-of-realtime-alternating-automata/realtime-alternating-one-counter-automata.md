# Realtime alternating one-counter automata

A realtime alternating one-counter automaton reads its input once, left to right, between end-markers, with existential and universal states and one integer counter that it can test for zero and change by $-1$, $0$ or $+1$ at each step.

Let $\Sigma$ be a finite input alphabet and let $\vdash,\dashv\notin\Sigma$ be end-markers; write $\tilde\Sigma=\Sigma\cup\{\vdash,\dashv\}$. An input $w\in\Sigma^*$ is read as $\vdash w\dashv$. A *realtime alternating finite automaton* (AFA) is a tuple $A=(S,\Sigma,\delta,s_1,s_a)$ where $S$ is a finite set of states, each declared existential or universal, $s_1\in S$ is the initial state, $s_a\in S$ is the accepting state and $\delta:S\times\tilde\Sigma\to\mathcal P(S)$. The head moves one symbol to the right per input symbol, and the automaton may spend at most two steps on each symbol, so that it can make an existential and a universal choice on the same symbol. A *realtime alternating one-counter automaton* (A1CA) adds an integer counter, initially $0$: its transition function is

$$
\delta: S\times\tilde\Sigma\times\{0,\pm\}\to\mathcal P\bigl(S\times\{-1,0,1\}\bigr),
$$

where the third argument says whether the counter is zero ($0$) or nonzero ($\pm$), and each chosen pair gives the next state and the increment added to the counter on that branch.

The computation on $w$ is a tree of configurations. A leaf is *true* when the computation ends, after reading $\dashv$, in the accepting state, and *false* otherwise; an existential node is true when some child is true and a universal node when all children are true. The automaton accepts $w$ when the root is true. The A1CA is *unary* when $|\Sigma|=1$. The *emptiness problem* asks, given an A1CA, whether it accepts no input.

## Depends on

None.

## Proof depends on

None.

## Expansion

The A1CA extends the realtime AFA, a realtime form of [alternating automata on finite words](../../../omega-automata-and-games/alternating-automata/alternating-automata-on-finite-words.md), which recognizes only regular languages, by one counter; realtime A1CAs recognize some unary nonregular languages, while realtime nondeterministic one-counter automata on unary inputs recognize only regular ones. Acceptance is the usual bottom-up evaluation of an alternating computation tree, which is finite because the automaton is realtime.

## Sources

- H. Gökalp Demirci, Mika Hirvensalo, Klaus Reinhardt, A. C. Cem Say and Abuzer Yakaryılmaz, "Alternating, private alternating, and quantum alternating realtime automata", *Logical Methods in Computer Science* 15(3), 2019, paper 22, doi:[10.23638/LMCS-15(3:22)2019](https://doi.org/10.23638/LMCS-15(3:22)2019); numbering of arXiv:1407.0334v5 ([arXiv](https://arxiv.org/abs/1407.0334v5)): Section 2, the definitions of realtime AFAs and A1CAs, and the conventions of Section 1 on end-markers and two steps per symbol.
