# One-counter automata and one-counter nets

A one-counter automaton is a nondeterministic finite automaton with a counter over the natural numbers that transitions may change by integer amounts, never below zero, and that zero tests may inspect. A one-counter net is the same model without zero tests.

**Definition.** A *one-counter automaton* (OCA) over a finite alphabet $\Sigma$ is a tuple $\mathcal{A} = (Q, \alpha_0, \alpha_f, T, T_{=0})$ where $Q$ is a finite set of control states, a *configuration* is a pair $(q, n) \in Q \times \mathbb{N}$, $\alpha_0 = (q_0, n_0)$ and $\alpha_f = (q_f, n_f)$ are the initial and final configurations, $T \subseteq Q \times (\Sigma \cup \{\varepsilon\}) \times Q \times \mathbb{Z}$ is a finite set of *transitions* and $T_{=0} \subseteq Q \times (\Sigma \cup \{\varepsilon\}) \times Q$ is a finite set of *zero tests*. A transition $(q, a, q', z)$ leads from $(q, n)$ to $(q', n + z)$ provided $n + z \ge 0$; a zero test $(q, a, q')$ leads from $(q, n)$ to $(q', n)$ only if $n = 0$. A run over $w \in \Sigma^*$ is a sequence of such steps whose labels, with $\varepsilon$ erased, spell $w$; it is accepting if it starts in $\alpha_0$ and ends in $\alpha_f$, and $L(\mathcal{A})$ is the set of words with an accepting run. A *one-counter net* (OCN) is an OCA with $T_{=0} = \emptyset$, that is, a vector addition system with states of dimension one.

Acceptance by a final configuration can simulate the other usual acceptance conditions, such as reaching a final state with any counter value.

## Depends on

None.

## Proof depends on

None.

## Sources

- W. Czerwiński and S. Lasota, "Regular separability of one counter automata", *Logical Methods in Computer Science* 15(2):20, 2019, doi:10.23638/LMCS-15(2:20)2019, <https://lmcs.episciences.org/4417>; numbering of arXiv:1701.02808v5: the definitions of nondeterministic finite automata, one counter automata and one counter nets in Section 2.
