# Emptiness of universal co-Büchi tree automata with qualitative semantics is undecidable

Under the qualitative semantics, a run on an infinite binary tree is accepting when almost every branch, for the coin-flipping measure, satisfies the acceptance condition. For universal co-Büchi tree automata with this semantics emptiness is undecidable, although for nondeterministic and alternating Büchi automata it is decidable.

**Theorem.** A *tree automaton* over an alphabet $\Sigma$ is $\mathcal A = (Q, q_{\mathrm{in}}, \Delta)$ with a finite set $Q$ of states, an initial state $q_{\mathrm{in}}$ and a transition relation $\Delta \subseteq Q \times \Sigma \times Q \times Q$. A *run* over a $\Sigma$-labeled infinite binary tree $t : \{0, 1\}^* \to \Sigma$ is a map $\rho : \{0, 1\}^* \to Q$ with $\rho(\varepsilon) = q_{\mathrm{in}}$ and $(\rho(u), t(u), \rho(u0), \rho(u1)) \in \Delta$ for every node $u$. Let $\mu$ be the coin-flipping measure on branches, with $\mu(u \cdot \{0, 1\}^\omega) = 2^{-|u|}$. For $F \subseteq Q$, a run is *qualitatively co-Büchi accepting* if the set of branches along which states of $F$ occur only finitely often has $\mu$-measure $1$. Under the *universal* semantics, $\mathcal A$ accepts the trees $t$ all of whose runs are qualitatively co-Büchi accepting. There is no algorithm that decides, given $\mathcal A$ and $F$, whether the set of trees accepted in this way is empty.

As consequences, the MSO+$\forall^{=1}_{\mathrm{path}}$ theory of the infinite binary tree, monadic second-order logic with a quantifier saying that almost all branches satisfy a formula, is undecidable (Theorem 5.1 of the source), and so is emptiness of alternating tree automata with non-zero semantics (Theorem 5.2). For alternating Büchi tree automata with qualitative semantics emptiness is decidable in exponential time (Theorem 3.7).

## Depends on

- [Tree automata on infinite trees](tree-automata-on-infinite-trees.md)

## Proof depends on

- [Value-1 problem for probabilistic automata](../../regular-languages/automata-and-expressions/weighted-automata-and-rational-series/value-1-problem-for-probabilistic-automata.md)

## Expansion

The proof starts from the undecidability of the value-1 problem for simple probabilistic word automata, in which every transition moves to one of two states with probability $\tfrac12$ each (Gimbert and Oualhadj, Theorem 2.5). It follows that emptiness of simple probabilistic co-Büchi word automata with almost-sure semantics is undecidable (Proposition 4.1). For the reduction, a simple probabilistic word automaton with transitions $\delta(p, a) = \tfrac12 q_1 + \tfrac12 q_2$ gives two probabilistic tree automata, one sending $q_1$ or $q_2$ to both children and one sending them to the two children in either order; Lemmas 4.3 and 4.4 relate almost-sure acceptance of a word by the word automaton to qualitative acceptance by these tree automata, and from them one builds a universal co-Büchi tree automaton whose qualitative language is nonempty iff the word automaton almost-surely accepts some word.

## Sources

- R. Berthon, N. Fijalkow, E. Filiot, S. Guha, B. Maubert, A. Murano, L. Pinault, S. Pinchinat, S. Rubin and O. Serre, "Alternating Tree Automata with Qualitative Semantics", *ACM Transactions on Computational Logic* 22(1):1–24, 2020, doi:[10.1145/3431860](https://doi.org/10.1145/3431860); read as arXiv:2002.03664v2, whose numbering is used here: Section 2.5 (tree automata, runs and the qualitative co-Büchi semantics), Theorem 2.5, Proposition 4.1, Theorem 4.2 with Lemmas 4.3 and 4.4, Theorem 3.7, Theorems 5.1 and 5.2.
