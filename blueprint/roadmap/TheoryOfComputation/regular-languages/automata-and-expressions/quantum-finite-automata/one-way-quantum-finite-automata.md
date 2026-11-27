# One-way quantum finite automata

A *one-way quantum finite automaton* over $\Sigma$ has a finite set $Q$ of basis states, an initial state $|q_1\rangle$, a transformation $T_\sigma$ of its quantum state
for each symbol $\sigma$ of $\Sigma$ extended with two end-markers, and an acceptance rule, typically a set $Q_a \subseteq Q$ of accepting states: at the end the state
is measured in the standard basis and the automaton accepts if the outcome lies in $Q_a$; $f_M(w)$ is the acceptance probability of $w$. In the
*Moore–Crutchfield* (measure-once) model every $T_\sigma$ is a unitary map and the only measurement is the final one; in the *Kondacs–Watrous*
model the state is also measured after every symbol against a partition into accepting, rejecting and non-halting states; general
models allow superoperators acting on mixed states. A language $L$ is recognized *with bounded error* if for some $\varepsilon < 1/2$,
$f_M(w) \ge 1 - \varepsilon$ for $w \in L$ and $f_M(w) \le \varepsilon$ for $w \notin L$. For example, the two-state automaton rotating by $2\pi/p$ on each $a$ accepts $a^j$ with
probability $\cos^2(2\pi j/p)$.

## Sources

- A. Ambainis and A. Yakaryılmaz, "Automata and quantum computing", in J.-É. Pin (ed.), *Handbook of Automata Theory*, EMS Press, 2021; arXiv:1507.01988: Section 4 (before Section 4.1), the general definition of 1QFAs, the example with Lemma 4.1, and the models (1) Moore–Crutchfield and (2) Kondacs–Watrous with the acceptance criteria.
