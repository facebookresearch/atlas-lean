# Automata with monitor counters

An automaton with $n$ monitor counters reads an infinite word and starts, increments and terminates integer counters without ever testing them. Each terminated counter contributes its final value at the position where it was started, and a value function such as $\sup$, $\limsup$ or limit average turns these values into the value of the run.

**Definition.** An *automaton with $n$ monitor counters* is a tuple $\langle \Sigma, Q, Q_0, \delta, F \rangle$ with a finite alphabet $\Sigma$, a finite set $Q$ of states, initial states $Q_0 \subseteq Q$, accepting states $F \subseteq Q$ and a finite transition relation $\delta \subseteq Q \times \Sigma \times Q \times (\mathbb{Z} \cup \{s, t\})^n$, such that every transition starts (letter $s$) at most one counter. A run on an infinite word $w = w[1] w[2] \cdots$ is a sequence $\pi[0] \pi[1] \cdots$ of elements of $Q \times (\mathbb{Z} \cup \{\bot\})^n$ with $\pi[0] = \langle q_0, \vec{\bot} \rangle$ for some $q_0 \in Q_0$ such that, for each $i > 0$ with $\pi[i-1] = \langle q, \vec{u} \rangle$ and $\pi[i] = \langle q', \vec{u}' \rangle$, some transition $(q, w[i], q', \vec{v})$ satisfies, for every counter $j$: if $v[j] = s$ then $u[j] = \bot$ and $u'[j] = 0$; if $v[j] = t$ then $u[j] \in \mathbb{Z}$ and $u'[j] = \bot$; and if $v[j] \in \mathbb{Z}$ then $u'[j] = u[j] + v[j]$ (with $\bot + v = \bot$). The automaton is *deterministic* if $Q_0$ is a singleton and $\delta$ is a function from $Q \times \Sigma$ to $Q \times (\mathbb{Z} \cup \{s, t\})^n$.

A run is *accepting* if some state of $F$ occurs infinitely often, some counter is started infinitely often, and every started counter is eventually terminated. An accepting run defines the sequence of integers obtained by recording, at each position where a counter is started, the value of that counter when it is next terminated (positions where no counter starts are skipped). For a value function $f$ on infinite sequences of integers, such as $\sup$, $\inf$, $\limsup$, $\liminf$ or the limit average, the *$f$-automaton with monitor counters* assigns to a run the value $f$ of this sequence, and to a word the infimum of the values of its accepting runs ($+\infty$ if it has none). The *emptiness problem* asks, given such an automaton $\mathcal{A}$ and $\lambda \in \mathbb{Q}$, whether some word $w$ has $\mathcal{A}(w) \le \lambda$.

Deterministic $f$-automata with monitor counters translate in polynomial time into deterministic nested weighted automata of bounded width with sum-valued slave automata, and conversely in exponential time; weights are given in unary.

## Depends on

None.

## Proof depends on

None.

## Sources

- K. Chatterjee, T. A. Henzinger and J. Otop, "Quantitative Automata under Probabilistic Semantics", *Logical Methods in Computer Science* 15(3):16, 2019, doi:10.23638/LMCS-15(3:16)2019, <https://lmcs.episciences.org/4512>; numbering of arXiv:1604.06764v4: the value functions in Section 2, Section 3.1 (automata with monitor counters and their semantics), the translation lemma in Section 3, and the emptiness problem in Section 4.1.
