# Equivalence of nondeterministic probabilistic automata is undecidable

Under either of the two convex language semantics that extend the expected-weight semantics of probabilistic automata, no algorithm decides whether two nondeterministic probabilistic automata over an alphabet with at least two letters assign the same weight to every word.

**Nondeterministic probabilistic automata.** A *nondeterministic probabilistic automaton* (NPA) over a finite alphabet $A$ is a tuple $(S, s_0, \gamma, \{\tau_a\}_{a \in A})$ with a finite set $S$ of states, an initial state $s_0$, an output function $\gamma \colon S \to [0, 1]$, and transition functions $\tau_a$ that map each state to a nonempty finitely generated convex set of probability distributions on $S$. On each letter the automaton chooses a distribution from the offered convex set and then moves probabilistically. Reading a word letter by letter from $s_0$, applying the transitions to every distribution reached and taking convex hulls, yields a finitely generated convex set of distributions on states; mapping each of these to its expected output weight gives a set of numbers in $[0, 1]$. The *max semantics* assigns to the word the maximum of this set, the *min semantics* its minimum. These are the only two semantics, defined through algebras for the convex powerset of distributions monad on $[0, 1]$, that agree with the expected weight of a deterministic probabilistic automaton when no nondeterministic choice is made.

**Theorem (van Heerdt, Hsu, Ouaknine and Silva).** If $|A| \ge 2$, then under the max semantics and under the min semantics there is no algorithm that decides, given two NPAs over $A$, whether they assign the same weight to every word.

The same paper shows that NPAs are strictly more expressive than deterministic probabilistic automata, and that a discounted distance between their languages can be approximated to any precision.

## Depends on

- [Probabilistic automata and cut-point languages](../probabilistic-automata-and-cut-point-languages.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../emptiness-problem-for-probabilistic-automata.md)

## Expansion

The proof reduces a threshold problem for deterministic probabilistic automata. Given such an automaton $X$ and $\kappa \in [0, 1]$, one forms an NPA $Y$ whose initial state has output $\kappa$ and, on every letter, may either move to a state that keeps output $\kappa$ forever or enter $X$, and an NPA $Z$ with a single state of output $\kappa$ looping on every letter. Then $Y$ and $Z$ both give weight $\kappa$ to the empty word, and on a word $av$ the automaton $Z$ gives $\kappa$ while $Y$ gives the maximum (or minimum) of $\kappa$ and the weight of $v$ in $X$. So under the max semantics $Y$ and $Z$ are equivalent if and only if $X$ gives every word weight at most $\kappa$, and under the min semantics if and only if $X$ gives every word weight at least $\kappa$. Both threshold problems are undecidable for alphabets with at least two letters (Blondel and Canterini, as the source recalls); the first is the complement of the emptiness problem for probabilistic automata.

## Sources

- G. van Heerdt, J. Hsu, J. Ouaknine and A. Silva, "Convex Language Semantics for Nondeterministic Probabilistic Automata", in *Theoretical Aspects of Computing (ICTAC 2018)*, Lecture Notes in Computer Science, Springer, 2018, pp. 472–492, doi:10.1007/978-3-030-02508-3_25, read as arXiv:1805.11550v1, <https://arxiv.org/abs/1805.11550v1>; journal version *Theoretical Computer Science* 1040, 2025, article 115191, doi:10.1016/j.tcs.2025.115191 (cited, not read): Theorem 5 (equivalence of NPAs is undecidable when $|A| \ge 2$ and the semantics extends the usual one) with its proof, Corollary 1 (the min and max semantics are the only ones), the definition of NPAs and the worked example of the min semantics in Section 3, and the abstract (expressiveness, discounted distance), in the numbering of that version.
