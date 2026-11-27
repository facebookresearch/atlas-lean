# Emptiness of nested data class memory automata is undecidable

No algorithm decides whether a nested data class memory automaton, which reads words whose data values form a forest and remembers a state for each data value and its ancestors, accepts some data word; the weak variant, in which every state is locally accepting, has decidable emptiness.

**Definitions.** A *nested data set* of level $l$ is a forest $\langle D, \mathrm{pred} \rangle$ of infinitely many rooted trees, where $\mathrm{pred}$ maps each non-root node to its parent, every node has level at most $l$ (roots have level $1$), and every node of level below $l$ has infinitely many children. A *nested data class memory automaton* (NDCMA) of level $l$ over a finite alphabet $\Sigma$ is a tuple $\langle Q, \Sigma, \delta, q_0, F_L, F_G \rangle$ with a finite set $Q$ of states, an initial state $q_0$, sets $F_G \subseteq F_L \subseteq Q$ of globally and locally accepting states, and a transition map $\delta = \bigcup_{1 \le i \le l} \delta_i$ with $\delta_i : Q \times \Sigma \times (\{i\} \times Q_\bot^{\,i}) \to \mathcal{P}(Q)$, where $Q_\bot = Q \cup \{\bot\}$. It reads words over $\Sigma \times D$. A configuration is a pair $(q, f)$ of a state and a *class memory function* $f : D \to Q_\bot$ with $f(d) = \bot$ for all but finitely many $d$; the initial configuration is $(q_0, f_0)$ with $f_0 \equiv \bot$. On reading $(a, d)$ with $d$ of level $i$, the automaton may move from $(q, f)$ to $(q', f')$ if

$$
q' \in \delta(q, a, (i, f(\mathrm{pred}^{i-1}(d)), \dots, f(\mathrm{pred}(d)), f(d))),
$$

where $f' = f[d \mapsto q, \mathrm{pred}(d) \mapsto q, \dots, \mathrm{pred}^{i-1}(d) \mapsto q]$, as in Definition 7 of the source. A run is accepting if it ends in a configuration $(q, f)$ with $q \in F_G$ and $f(d) \in F_L \cup \{\bot\}$ for every $d$. The NDCMA is *weak* if $F_L = Q$. Level-$1$ NDCMA are equivalent to ordinary class memory automata over (non-nested) data words.

**Theorem.** The emptiness problem for nested data class memory automata is undecidable. Emptiness of weak nested data class memory automata is decidable, but Ackermann-hard.

Level-$1$ NDCMA are ordinary class memory automata, whose emptiness is decidable, being equivalent to reachability in Petri nets; the encoding of reset nets used in the proof needs data values of level $2$.

## Depends on

- [Register automata on data words](register-automata-on-data-words.md)

## Proof depends on

None.

## Expansion

Undecidability follows by encoding reachability in Petri nets with reset arcs, which is undecidable (Araki and Kasami). As for class memory automata, tokens are encoded by data values whose remembered state records their location; in the nested setting each place has a level-$1$ data value acting as a bag, and its tokens are level-$2$ data values nested under it. A reset arc is simulated by moving the place's current level-$1$ data value to a dead state, from which neither it nor its children move again, and continuing with a fresh level-$1$ data value for the place. For weak automata the same encoding reduces coverability in reset nets, which gives Ackermann-hardness (Schnoebelen), while decidability comes from a well-structured transition system on forests of labelled trees of bounded depth.

## Sources

- C. Cotton-Barratt, A. S. Murawski and C.-H. L. Ong, "Weak and Nested Class Memory Automata", in *Language and Automata Theory and Applications (LATA 2015)*, Lecture Notes in Computer Science 8977, pp. 188–199, 2015, doi:[10.1007/978-3-319-15579-1_14](https://doi.org/10.1007/978-3-319-15579-1_14). Read in arXiv:1409.1136v2 ([arXiv](https://arxiv.org/abs/1409.1136v2)), whose numbering is used here: Section 2 (class memory automata and the equivalence of their emptiness with Petri net reachability), Definitions 6 and 7 (nested data sets and NDCMA), Example 8 (encoding Petri nets with reset arcs) and Theorem 9.
