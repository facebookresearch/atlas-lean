# Equivalence of deterministic Büchi transducers is undecidable

No algorithm decides whether two deterministic Büchi transducers define the same relation between infinite words, for relations of any arity $k \ge 2$, although equivalence of deterministic transducers over finite words is decidable.

**Definitions.** A *$k$-ary transducer* $\mathcal{A} = (Q, \Sigma_1, \dots, \Sigma_k, q_0, \Delta, F)$ has a finite state set $Q$, finite alphabets $\Sigma_1, \dots, \Sigma_k$, an initial state $q_0$, accepting states $F \subseteq Q$ and transitions $\Delta \subseteq Q \times (\Sigma_1 \cup \{\varepsilon\}) \times \cdots \times (\Sigma_k \cup \{\varepsilon\}) \times Q$. A run on a tuple $(u_1, \dots, u_k)$ of infinite words $u_j \in \Sigma_j^\omega$ is an infinite sequence of states $p_0 p_1 \cdots$ for which the tuple decomposes into consecutive transition labels; it is accepting (Büchi condition) if $p_0 = q_0$ and some state of $F$ occurs infinitely often, and $R_\omega(\mathcal{A}) \subseteq \Sigma_1^\omega \times \cdots \times \Sigma_k^\omega$ is the set of tuples with an accepting run, an *$\omega$-rational relation*. The transducer is *deterministic* if $Q$ is partitioned as $Q_1 \cup \cdots \cup Q_k$, a state in $Q_j$ reads only the $j$-th component, and $\Delta$ is a partial function $\bigcup_j Q_j \times (\Sigma_j \cup \{\varepsilon\}) \to Q$ in which a state with an $\varepsilon$-transition has no other transition. The *equivalence problem* asks, given two deterministic Büchi transducers $\mathcal{A}, \mathcal{B}$ of the same arity and alphabets, whether $R_\omega(\mathcal{A}) = R_\omega(\mathcal{B})$.

**Theorem.** For every $k \ge 2$, the equivalence problem for $k$-ary $\omega$-rational relations given by deterministic Büchi transducers is undecidable.

For relations over finite words, equivalence of deterministic transducers is decidable (Bird; Harju and Karhumäki), so the theorem marks a difference between finite and infinite words.

## Depends on

- [Rational relations and transducers](../rational-relations-and-transducers.md)
- [Büchi acceptance condition](../../../../omega-automata-and-games/emptiness-of-b-chi-automata/mem-language-iff.md)

## Proof depends on

None.

## Expansion

The proof is a many-one reduction from the intersection emptiness problem for binary relations over finite words given by deterministic transducers (with an end marker $\#$), which is undecidable (Rabin and Scott; Berstel) by a reduction from the Post correspondence problem. It suffices to treat $k = 2$, since dummy components extend the result to higher arities. Given deterministic transducers $\mathcal{A}_R, \mathcal{A}_S$ for relations $R, S$ in a normal form with a unique accepting and a unique rejecting state, each entered only on $\#$ and without outgoing transitions, one builds two deterministic Büchi transducers $\mathcal{B}_R$ and $\mathcal{B}_S$ on the alphabets extended by $\#$ that share the union of the two transition structures and differ only in their initial state ($q_0^R$, respectively $q_0^S$): from the accepting state of either part the run continues as from that part's initial state, from the rejecting state of either part it continues as from the other part's initial state, and the Büchi states are the accepting and rejecting states of $\mathcal{A}_R$ and the rejecting state of $\mathcal{A}_S$. A pair $(u, v) \in R \cap S$ gives the input $(u\#, v\#)^\omega$, accepted by $\mathcal{B}_R$ and rejected by $\mathcal{B}_S$; conversely, a pair of infinite words on which they differ contains infinitely many $\#$ in both components, and the asymmetry between the two accepting states forces some block $(u\#, v\#)$ with $(u, v) \in R \cap S$. Hence $R \cap S \ne \emptyset$ if and only if $R_\omega(\mathcal{B}_R) \ne R_\omega(\mathcal{B}_S)$. The construction follows one used for the undecidability of equivalence of one-counter Büchi automata.

## Sources

- C. Löding and C. Spinrath, "Decision Problems for Subclasses of Rational Relations over Finite and Infinite Words", *Discrete Mathematics & Theoretical Computer Science* 21(3), Automata, Logic and Semantics, 2019, Article 4, doi:[10.23638/DMTCS-21-3-4](https://doi.org/10.23638/DMTCS-21-3-4); numbering of arXiv:1803.06140v5: the definitions of transducers, determinism and Büchi acceptance in Section 2, Proposition 1 (intersection emptiness for deterministic transducers, quoted from Rabin–Scott and Berstel) and Theorem 2 with its proof in Section 3.
