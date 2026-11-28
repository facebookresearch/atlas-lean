# Weak detectability of labeled timed automata is undecidable

No algorithm decides whether a labeled timed automaton has some infinite behavior along which an observer of the timed labels eventually always knows the current state, nor the periodic version of this property.

**Labeled timed automata.** A *labeled timed automaton* $(Q, E, Q_0, C, \Delta, \Sigma, \ell)$ has finite sets $Q$ of states, $E$ of events and $C$ of clocks, initial states $Q_0 \subseteq Q$, edges $\Delta \subseteq Q \times E \times Q \times 2^C \times \Phi(C)$ with clock constraints built from $x \le c$ and $c \le x$ ($c$ a nonnegative rational) by negation and conjunction, and a labeling $\ell \colon E \to \Sigma \cup \{\varepsilon\}$. Runs alternate delays and edges as for timed automata, starting from an initial state with all clocks $0$; $L^\omega$ is the set of $\omega$-timed words of infinite runs. The observation of a run is the sequence of labels of its observable events with their global time stamps. For a timed label sequence $\gamma$, the *current-state estimate* $\mathcal{M}(\gamma)$ is the set of states reachable from $Q_0$ by a finite run whose observation is $\gamma$, with no time elapsing after the last observable event.

**Weak detectability.** The automaton is *weakly detectable* if, when $L^\omega$ is nonempty, there are $t \in \mathbb{Z}_+$ and some $\omega$-timed word $w \in L^\omega$ such that $|\mathcal{M}(\gamma)| = 1$ for every prefix $\gamma$ of $\ell(w)$ of length at least $t$. It is *weakly periodically detectable* if, when $L^\omega$ is nonempty, there are $t \in \mathbb{Z}_+$ and some $w \in L^\omega$ such that every prefix $w'$ of $w$ extends to a prefix $w' w''$ of $w$ with $|\ell(w'')| < t$ and $|\mathcal{M}(\ell(w' w''))| = 1$.

An automaton with $L^\omega = \varnothing$ counts as weakly detectable and weakly periodically detectable (Definitions 12 and 13 of the source).

**Theorem (Zhang).** Weak detectability and weak periodic detectability of labeled timed automata are undecidable (Theorem 17 of the source). This holds already for automata with two states, both initial, one event, which is observable, and clock constants $0$ and $1$: the proof reduces from the universality problem for timed automata with a single state, a single event and clock constants $0$ and $1$, which Adams, Ouaknine and Worrell showed undecidable, a restricted variant of the universality problem of Alur and Dill.

Deterministic timed automata satisfy every detectability notion; the same paper characterizes strong detectability by region automata (Theorem 15) and shows its verification PSPACE-complete (Theorem 16).

## Depends on

- [Timed Büchi automata and timed regular languages](timed-buchi-automata.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces universality of timed automata with a single state, a single event and clock constants $0$ and $1$ only, which is undecidable (Adams, Ouaknine and Worrell). One adds to such an automaton a new initial state with an unconstrained self-loop on the event, which yields a deterministic automaton accepting all timed words, and takes the disjoint union of this automaton with the given one, the event being observable. If some timed word $w$ is rejected by the given automaton, then along $w$ followed by further events the current-state estimate eventually becomes the new initial state alone; hence the union is not weakly (periodically) detectable exactly when the given automaton accepts every timed word. A good expansion links a page for the undecidability of universality of one-state, one-event timed automata with clock constants $0$ and $1$ (Adams, Ouaknine and Worrell).

## Sources

- K. Zhang, "Detectability of labeled weighted automata over monoids", *Discrete Event Dynamic Systems* 32(3) (2022), pp. 435–494, doi:10.1007/s10626-022-00362-8; read as arXiv:2006.14164v7, <https://arxiv.org/abs/2006.14164v7>: Theorem 17 (weak and weak periodic detectability of timed automata are undecidable) with its proof, Problem 3 and Lemma 5 (universality of single-state timed automata), Definitions 12 and 13, and the notation of labeled timed automata, runs and current-state estimates in the section on detectability in labeled timed automata, in the numbering of that version.
