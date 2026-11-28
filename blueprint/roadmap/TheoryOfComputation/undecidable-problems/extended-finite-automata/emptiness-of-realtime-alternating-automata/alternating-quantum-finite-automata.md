# Alternating quantum finite automata

An alternating quantum finite automaton is a realtime automaton with a classical control of existential and universal states and a finite-dimensional quantum register; each step applies a superoperator, and each outcome of nonzero probability opens a branch of an alternating computation tree.

**Quantum finite automata.** Let $\Sigma$ be a finite input alphabet with end-markers $\vdash,\dashv$ and $\tilde\Sigma=\Sigma\cup\{\vdash,\dashv\}$. A (realtime) *quantum finite automaton* (QFA) is a tuple $M=(Q,\Sigma,\{\mathcal E_\sigma:\sigma\in\tilde\Sigma\},|v_0\rangle,P)$ where $Q=\{q_1,\dots,q_n\}$, each $\mathcal E_\sigma=\{E_{\sigma,1},\dots,E_{\sigma,l_\sigma}\}$ is a superoperator given by $n\times n$ operation elements with $\sum_k E_{\sigma,k}^\dagger E_{\sigma,k}=I$, $|v_0\rangle$ is a basis state and $P=\{P_a,P_r\}$ is a projective measurement applied after $\dashv$. On $\vdash w\dashv=\sigma_1\cdots\sigma_m$ the density matrix evolves as $\rho_j=\sum_k E_{\sigma_j,k}\,\rho_{j-1}E_{\sigma_j,k}^\dagger$ from $\rho_0=|v_0\rangle\langle v_0|$, and the acceptance probability is $f_M(w)=\operatorname{Tr}(P_a\rho_m)$. A *nondeterministic* QFA (NQFA) accepts $L=\{w: f_M(w)>0\}$; a *universal* QFA (UQFA) accepts $L=\{w: f_M(w)=1\}$.

**Alternation.** An *alternating quantum finite automaton* (AQFA) has a finite set of classical states, each existential or universal, with an initial and a set of accepting classical states, and a quantum register as above. On each step, in the quantum phase, a superoperator chosen by the current symbol and classical state is applied to the current pure quantum state, and every operation element $E_k$ whose outcome has nonzero probability opens a branch carrying the normalized state $E_k|\psi\rangle/\lVert E_k|\psi\rangle\rVert$; in the classical phase, the next classical state is a function of the symbol, the classical state and the outcome. As in the classical realtime models, at most two steps are spent on each input symbol. The computation is a tree whose nodes are pairs (classical state, pure quantum state); only whether a probability is nonzero matters, not its value. A leaf is true when the computation ends in an accepting classical state after $\dashv$; an existential node is true when some child is, a universal node when all children are; the input is accepted when the root is true. NQFAs and UQFAs are the AQFAs whose classical states are all existential, respectively all universal. The *emptiness problem* asks whether the automaton accepts no input.

## Depends on

None.

## Proof depends on

None.

## Expansion

Classical realtime alternation, as in [alternating automata on finite words](../../../omega-automata-and-games/alternating-automata/alternating-automata-on-finite-words.md), is the special case of a one-dimensional quantum register, and the unitary model of [one-way quantum finite automata](../../../regular-languages/automata-and-expressions/quantum-finite-automata/one-way-quantum-finite-automata.md) is the special case of a single unitary operation element per symbol. NQFAs and UQFAs recognize the exclusive and co-exclusive stochastic languages, which contain no nonregular unary language; with two alternations an AQFA recognizes the unary squares $\{a^{n^2}\}$. Emptiness for NQFAs with algebraic amplitudes is decidable (Theorem 4.1 of the source).

## Sources

- H. Gökalp Demirci, Mika Hirvensalo, Klaus Reinhardt, A. C. Cem Say and Abuzer Yakaryılmaz, "Alternating, private alternating, and quantum alternating realtime automata", *Logical Methods in Computer Science* 15(3), 2019, paper 22, doi:[10.23638/LMCS-15(3:22)2019](https://doi.org/10.23638/LMCS-15(3:22)2019); numbering of arXiv:1407.0334v5 ([arXiv](https://arxiv.org/abs/1407.0334v5)): Section 4, the definitions of QFAs, NQFAs, UQFAs and AQFAs, Theorem 4.1 (NQFA emptiness decidable) and Theorem 4.3 (unary squares).
