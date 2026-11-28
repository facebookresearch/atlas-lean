# Blind alternating finite automata

A blind alternating finite automaton is a realtime automaton with universal branching that also reads, one way, a certificate supplied by an existential player who cannot see the input; it accepts a word when some certificate makes every branch accept.

Let $\Sigma$ be a finite input alphabet with end-markers $\vdash,\dashv\notin\Sigma$, $\tilde\Sigma=\Sigma\cup\{\vdash,\dashv\}$. A *blind alternating finite automaton* (BAFA) is a tuple $B=(U,\Sigma,\Gamma,\delta,u_1,U_a)$ where $U$ is a finite set of (universal) states, $\Gamma$ is a finite certificate alphabet with a blank symbol $\#\notin\Gamma$, $u_1\in U$ is the initial state, $U_a\subseteq U$ is the set of accepting states and

$$
\delta: U\times\tilde\Sigma\times(\Gamma\cup\{\#\})\to\mathcal P\bigl(U\times\{0,1\}\bigr).
$$

On an input $w\in\Sigma^*$, written $\vdash w\dashv$ on a realtime input tape, and a finite certificate $c\in\Gamma^*$, written $c\#\#\cdots$ on a one-way read-only certificate tape, the automaton in state $u$ reading $\sigma$ and $\gamma$ branches universally into all pairs $(u',d)\in\delta(u,\sigma,\gamma)$: it enters $u'$, moves the input head one cell right, and moves the certificate head one cell right if $d=1$ and leaves it in place if $d=0$. A branch accepts if it is in a state of $U_a$ after reading $\dashv$; $B$ *accepts $w$ with certificate $c$* if every branch accepts. The language of $B$ is the set of $w$ for which some certificate $c\in\Gamma^*$ makes $B$ accept $w$. The *emptiness problem* asks, given a BAFA, whether its language is empty.

Equivalently, a BAFA is a realtime private alternating finite automaton whose universal part only ever hands one fixed state to the existential part, so that an existential strategy is a single sequence of existential choices, the certificate.

## Depends on

None.

## Proof depends on

None.

## Expansion

Blind alternation is the one-way analogue of a one-way interactive proof: the prover's messages do not depend on the verifier's universal choices, so they can be written in advance on a certificate tape. BAFAs recognize every regular language and some nonregular ones, such as $\{a^nb^n: n>0\}$, $\{w2w : w\in\{0,1\}^*\}$ and the unary squares $\{1^{n^2}: n\ge 0\}$.

## Sources

- H. Gökalp Demirci, Mika Hirvensalo, Klaus Reinhardt, A. C. Cem Say and Abuzer Yakaryılmaz, "Alternating, private alternating, and quantum alternating realtime automata", *Logical Methods in Computer Science* 15(3), 2019, paper 22, doi:[10.23638/LMCS-15(3:22)2019](https://doi.org/10.23638/LMCS-15(3:22)2019); numbering of arXiv:1407.0334v5 ([arXiv](https://arxiv.org/abs/1407.0334v5)): Section 3, the two definitions of BAFAs (as restricted private alternating automata and with a certificate tape), Corollary 3.2, Lemmas 3.1 and 3.3 and Theorem 3.6 (languages recognized).
