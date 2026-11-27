# Distributed automata

A distributed automaton is a deterministic finite-state machine copied onto every node of a finite labeled directed graph; in
synchronous rounds each node updates its state from its own state and the set of states of its incoming neighbors, and a
pointed graph is accepted if its distinguished node ever reaches an accepting state.

**Graphs.** Let $\Sigma$ be a finite alphabet and $r \ge 1$. A *$\Sigma$-labeled, $r$-relational directed graph* is a structure
$G = (V, (E_k)_{1 \le k \le r}, \lambda)$ with a finite nonempty set $V$ of nodes, edge relations $E_k \subseteq V \times V$ and a
labeling $\lambda : V \to \Sigma$; isomorphic graphs are identified. A *pointed* graph $(G, v)$ has a distinguished node $v$. A
*directed path* is a pointed graph that is $1$-relational, in which every node has at most one incoming neighbor, and in which
every node reaches the distinguished node, the root, by exactly one directed path.

**Automata and runs.** A *distributed automaton* over $\Sigma$-labeled $r$-relational graphs is a tuple
$\mathcal{A} = (Q, q_0, (\delta_a)_{a \in \Sigma}, F)$ with a finite nonempty set $Q$ of states, an initial state $q_0$, local
transition functions $\delta_a : Q \times (2^Q)^r \to Q$ and accepting states $F \subseteq Q$. Its *run* on $G$ is the sequence
$\rho_0, \rho_1, \dots$ of maps $V \to Q$ with $\rho_0(v) = q_0$ and

$$
\rho_{t+1}(v) = \delta_{\lambda(v)}\Bigl(\rho_t(v),\ \bigl(\{\rho_t(u) : (u, v) \in E_k\}\bigr)_{1 \le k \le r}\Bigr) .
$$

$\mathcal{A}$ *accepts* $(G, v)$ if $\rho_t(v) \in F$ for some $t \in \mathbb{N}$; its language is the set of pointed graphs it accepts.
In the $1$-relational case the label can be stored in the state, and an automaton is also written as $(Q, \iota, \delta, F)$ with an
initialization $\iota : \Sigma \to Q$ and one transition function $\delta : Q \times 2^Q \to Q$. The automaton is *quasi-acyclic* if
its state diagram contains no directed cycles other than self-loops: whenever $q_1, \dots, q_n$ with $q_1 = q_n$ satisfy
$\delta(q_i, S_i) = q_{i+1}$ for some sets $S_i \subseteq Q$, all the $q_i$ are equal.

**Problems.** The *emptiness problem* asks, for an automaton $\mathcal{A}$, whether some pointed graph is accepted; the
*directed-path emptiness problem* asks whether some pointed directed path is accepted.

## Depends on

None.

## Proof depends on

None.

## Sources

- A. Kuusisto and F. Reiter, "Emptiness problems for distributed automata", *Information and Computation* 272, article 104503, 2020, doi:10.1016/j.ic.2019.104503; conference version in *GandALF 2017*, Electronic Proceedings in Theoretical Computer Science 256, pp. 210–222, 2017, doi:10.4204/EPTCS.256.15. Section 2 of the version arXiv:1705.02609v2 (graphs, directed paths, Definition 1, runs, acceptance, the emptiness problems) and Section 6 (quasi-acyclic automata).
