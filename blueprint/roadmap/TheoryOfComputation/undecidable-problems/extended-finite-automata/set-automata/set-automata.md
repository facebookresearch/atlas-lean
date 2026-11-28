# Set automata

A set automaton is a one-way finite automaton with a work tape and a set of words as storage: it writes a word on the work tape and then inserts it into the set, removes it from the set, or tests whether it belongs to the set, after which the work tape is erased.

**Definition (Kutrib, Malcher and Wendlandt).** A *set automaton* is a tuple $M = \langle S, \Sigma, \Gamma, \lhd, \delta, s_0, F \rangle$ with a finite set $S$ of states, a finite input alphabet $\Sigma$, a finite work-tape alphabet $\Gamma$, a right endmarker $\lhd \notin \Sigma$, an initial state $s_0$, accepting states $F \subseteq S$ and a transition relation

$$
\delta \subseteq S \times (\Sigma \cup \{\varepsilon, \lhd\}) \times \bigl[ S \times (\Gamma^* \cup \{\mathbf{in}, \mathbf{out}\}) \ \cup\ S \times \{\mathbf{test}\} \times S \bigr].
$$

A configuration $(s, v, z, \mathbb{S})$ consists of a state, the unread input $v$, the work-tape content $z \in \Gamma^*$ and a finite set $\mathbb{S} \subseteq \Gamma^*$. Reading $x \in \Sigma \cup \{\varepsilon, \lhd\}$, a transition $(s, x, (s', z'))$ appends $z'$ to the work tape; $(s, x, (s', \mathbf{in}))$ inserts $z$ into $\mathbb{S}$, $(s, x, (s', \mathbf{out}))$ removes $z$ from $\mathbb{S}$, and $(s, x, (s_+, \mathbf{test}, s_-))$ moves to $s_+$ if $z \in \mathbb{S}$ and to $s_-$ otherwise; each of these three query operations erases the work tape. A word $w$ is accepted if some run from $(s_0, w\lhd, \varepsilon, \emptyset)$ reads the whole input including the endmarker and ends in a state of $F$. The automaton is *deterministic* (a DSA) if $\delta$ is a partial function and an $\varepsilon$-move from a state excludes moves on input letters from it; in general it is *nondeterministic* (an NSA).

## Depends on

None.

## Proof depends on

None.

## Expansion

This page states a definition. Deterministic set automata accept languages in P, and nondeterministic ones accept languages in NP, including NP-complete ones (Rubtsov and Vyalyi).

## Sources

- M. Kutrib, A. Malcher and M. Wendlandt, "Set automata", International Journal of Foundations of Computer Science 27 (2016), no. 2, 187–214, https://doi.org/10.1142/S0129054116400062 (cited beside the paper below, which restates the definition).
- A. A. Rubtsov and M. N. Vyalyi, "On computational complexity of set automata", Information and Computation 281 (2021), article 104797, https://doi.org/10.1016/j.ic.2021.104797; read in arXiv:1704.03730v2 (Section 1.1 of arXiv:1704.03730v2).
