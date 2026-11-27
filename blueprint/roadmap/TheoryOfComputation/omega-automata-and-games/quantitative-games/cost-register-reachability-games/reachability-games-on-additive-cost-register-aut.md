# Reachability games on additive cost register automata

An additive cost register automaton reads a word deterministically while updating integer registers by copy-and-add instructions
and outputs a register plus a constant; in the game version the system picks input symbols, the environment picks among
transitions, and the system wants to reach an accepting state with output within a budget.

**Automata.** An *additive cost register automaton* (ACRA) $M = (Q, \Sigma, V, \delta, \mu, q_0, F, \nu)$ has a finite set $Q$ of states, a
finite input alphabet $\Sigma$, a finite set $V$ of registers, a transition function $\delta : Q \times \Sigma \to Q$, a register update function
$\mu : Q \times \Sigma \times V \to V \times \mathbb{Z}$, a start state $q_0$, a nonempty set $F$ of accepting states and an output function
$\nu : F \to V \times \mathbb{Z}$. On reading $a$ in state $q$, each register $u$ with $\mu(q, a, u) = (v, c)$ receives the old value of $v$ plus $c$
(the update $u := v + c$, without tests). Starting with all registers $0$, the automaton maps a word to $\mathrm{val}(v) + c$ if it ends in a
state $q_f \in F$ with $\nu(q_f) = (v, c)$, and to "undefined" otherwise. With registers ranging over a domain $\mathbb{D} \in \{\mathbb{N}, \mathbb{Z}\}$
the model is written $\mathrm{ACRA}(\mathbb{D})$.

**Games.** An $\mathrm{ACRA}(\mathbb{D})$ *reachability game* is played on $G = (Q, \Sigma, V, \delta, \mu, q_0, F, \nu)$ as above except that
$\delta \subseteq Q \times \Sigma \times Q$ is a relation and $\mu : \delta \times V \to V \times \mathbb{D}$ updates registers per transition. In
configuration $(q, \mathrm{val})$ the system chooses a symbol $a$ and the environment chooses a transition $q \to^a q'$ in $\delta$, which updates
the registers. A strategy maps the history of states to the next symbol. A strategy is *winning with budget* $k \in \mathbb{D}$ from a
configuration if on every run consistent with it some configuration $(q_i, \mathrm{val}_i)$ has $q_i \in F$ and output
$\nu(q_i, \mathrm{val}_i) = \mathrm{val}_i(v) + c \le k$, where $\nu(q_i) = (v, c)$; the system may stop in such a configuration. The problem asks whether
the system has a winning strategy with budget $k$ from the initial configuration.

## Depends on

None.

## Proof depends on

None.

## Sources

- R. Alur and M. Raghothaman, "Decision problems for additive regular functions", in *Automata, Languages, and Programming (ICALP 2013), Part II*, Lecture Notes in Computer Science 7966, pp. 37–48, Springer, 2013, doi:10.1007/978-3-642-39212-2_7; read in arXiv:1304.7029v1: the definition of ACRAs in Section 2 and the definition of $\mathrm{ACRA}(\mathbb{D})$ reachability games at the start of Section 5.
