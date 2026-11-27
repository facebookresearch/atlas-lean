# The big-O problem for weighted automata is undecidable, even for labeled Markov chains

No algorithm decides, given a non-negative rational weighted automaton and two of its states $s, s'$, whether the weight of every word from $s$ is at most a constant multiple of its weight from $s'$; this holds already when the automaton is a labeled Markov chain.

**Definitions.** A *non-negative weighted automaton* $\mathcal{W} = \langle Q, \Sigma, M, F \rangle$ over $(\mathbb{Q}, +, \times)$ has a finite set $Q$ of states, a finite alphabet $\Sigma$, a transition weighting $M : \Sigma \to \mathbb{Q}^{Q \times Q}$ with $M(a)(q, q') \ge 0$, and a set $F \subseteq Q$ of final states; weights are given in binary as pairs of integers. The *weight* of $w = a_1 \cdots a_n$ from $s \in Q$ is

$$
\nu_s(w) = \sum_{t \in F} \big( M(a_1) M(a_2) \cdots M(a_n) \big)_{s, t},
$$

with $\nu_s(\varepsilon) = 1$ if $s \in F$ and $0$ otherwise. The state $s$ is *big-O of* $s'$ if there is $C > 0$ with $\nu_s(w) \le C \cdot \nu_{s'}(w)$ for all $w \in \Sigma^*$. The *big-O problem* asks, given $\mathcal{W}$ and $s, s' \in Q$, whether $s$ is big-O of $s'$. A *labeled Markov chain* is a non-negative weighted automaton in which $\sum_{q' \in Q} \sum_{a \in \Sigma} M(a)(q, q') = 1$ for every $q \notin F$ and final states have no outgoing transitions, so that $\nu_s$ is a subprobability distribution on $\Sigma^*$.

**Theorem.** The big-O problem is undecidable, even when the input automaton is a labeled Markov chain.

On labeled Markov chains, $s$ is big-O of $s'$ exactly when the multiplicative (ratio) total variation distance $\sup_{E \subseteq \Sigma^*} \nu_s(E) / \nu_{s'}(E)$ is finite, which is the existence of some level of $\varepsilon$-differential privacy between $s$ and $s'$. The same theorem of the source shows that deciding thresholds for this distance, even under the promise that it is finite, and approximating it are undecidable. The big-O problem is decidable in polynomial time for unambiguous automata and $\mathbf{coNP}$-complete over a one-letter alphabet.

## Depends on

- [Weighted automata over a semiring](../weighted-automata-over-a-semiring.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../emptiness-problem-for-probabilistic-automata.md)

## Expansion

The proof reduces the emptiness problem for probabilistic automata with cut-point $\frac{1}{2}$: given a probabilistic automaton $\mathcal{A}$, is $\mathrm{Pr}_{\mathcal{A}}(w) \le \frac{1}{2}$ for every word $w$? Assume without loss of generality that the start state $q_s$ of $\mathcal{A}$ is not accepting. The labeled Markov chain has two branches over the alphabet $\{a, b, \mathrm{acc}, \mathrm{rej}, \vdash\}$ (for $\Sigma = \{a, b\}$) and a single final state $t$: one branch simulates $\mathcal{A}$ with all weights scaled by $\frac{1}{4}$, an accepting state restarting at $q_s$ on $\mathrm{acc}$ and a rejecting state moving to $t$ on $\mathrm{rej}$, each with weight $\frac{1}{2}$; the other branch, from $s_0$, reads $a$, $b$ and $\mathrm{acc}$ in a loop and $\mathrm{rej}$ to $t$, each with weight $\frac{1}{4}$. Finally $s$ moves on $\vdash$ to $s_0$ and to $q_s$ with weight $\frac{1}{2}$ each, and $s'$ moves on $\vdash$ to $s_0$ with weight $1$. If some word $w$ has $\mathrm{Pr}_{\mathcal{A}}(w) > \frac{1}{2}$, the words ${\vdash}(w\,\mathrm{acc})^i\,\mathrm{rej}$ make $\nu_s / \nu_{s'}$ grow without bound, so $s$ is not big-O of $s'$; if $\mathcal{A}$ accepts no word with probability above $\frac{1}{2}$, the ratio stays at most $2$. A third state that enters the simulating branch with weight $\frac{1}{100}$ gives a promise gap (ratio at most $2$ versus between $49$ and $51$), from which the threshold and approximation results follow.

## Sources

- D. Chistikov, S. Kiefer, A. S. Murawski and D. Purser, "The Big-O Problem", *Logical Methods in Computer Science* 18(1):40, 2022, doi:10.46298/lmcs-18(1:40)2022, <https://lmcs.episciences.org/7343>; numbering of arXiv:2007.07694v6: the definitions in Section 2 (weighted automata, the big-O problem, labeled Markov chains), Observation 3.1 (the ratio total variation distance), and Theorem 4.2 with its proof in Section 4.
