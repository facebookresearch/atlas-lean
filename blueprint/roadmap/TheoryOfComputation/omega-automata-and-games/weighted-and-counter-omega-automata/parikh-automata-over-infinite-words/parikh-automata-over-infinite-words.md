# Parikh automata over infinite words

A Parikh automaton is a finite automaton whose transitions also carry vectors of natural numbers; over infinite words, a run is accepting when accepting states and prefix sums in a semilinear set occur together according to a safety, reachability, Büchi or co-Büchi condition.

**Definition.** Let $\Sigma$ be an alphabet, $d \ge 1$ and $D \subseteq \mathbb N^d$ finite. A *Parikh automaton* (PA) is a pair $(\mathcal A, C)$ where $\mathcal A = (Q, \Sigma \times D, q_I, \Delta, F)$ is a nondeterministic finite automaton over $\Sigma \times D$ and $C \subseteq \mathbb N^d$ is [semilinear](../../../context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md). It is *deterministic* if for each state $q$ and letter $a \in \Sigma$ there is at most one pair $(q', \vec v)$ with $(q, (a, \vec v), q') \in \Delta$. An infinite run $(q_0, w_0, q_1)(q_1, w_1, q_2) \cdots$ of $\mathcal A$ with $q_0 = q_I$ processes the projection to $\Sigma$ of $w_0 w_1 \cdots$; write $\Phi_n$ for the sum of the vectors of $w_0 \cdots w_{n-1}$. The run is

- *safety accepting* if $\Phi_n \in C$ and $q_n \in F$ for all $n \ge 1$;
- *synchronous reachability accepting* if $\Phi_n \in C$ and $q_n \in F$ for some $n \ge 1$;
- *asynchronous reachability accepting* if $\Phi_n \in C$ for some $n \ge 1$ and $q_{n'} \in F$ for some $n' \ge 1$;
- *synchronous Büchi accepting* if $\Phi_n \in C$ and $q_n \in F$ for infinitely many $n$;
- *asynchronous Büchi accepting* if $\Phi_n \in C$ for infinitely many $n$ and $q_{n'} \in F$ for infinitely many $n'$;
- *co-Büchi accepting* if there is $n_0$ with $\Phi_n \in C$ and $q_n \in F$ for all $n > n_0$.

The corresponding automata are safety (SPA), synchronous and asynchronous reachability (sRPA, aRPA), synchronous and asynchronous Büchi (sBPA, aBPA) and co-Büchi (CPA) Parikh automata, each accepting the infinite words over $\Sigma$ processed by an accepting run.

## Depends on

- [Semilinear set](../../../context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md)

## Proof depends on

None.

## Expansion

All these acceptance conditions are conjunctive: acceptance needs accepting states and prefix sums in $C$ together; a disjunctive variant is equivalent, since whether a prefix ends in an accepting state can be recorded in the vectors and folded into $C$. For example, with one state, the letters $a$ and $b$ counted in two coordinates and $C = \{(n, n)\}$, the safety automaton accepts no word and the reachability automaton every word, since the empty prefix is balanced and every odd-length prefix is not.

## Sources

- S. Guha, I. Jecker, K. Lehtinen and M. Zimmermann, "Parikh Automata over Infinite Words", in *42nd IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2022)*, Leibniz International Proceedings in Informatics 250, Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2022, article 40, doi:[10.4230/LIPIcs.FSTTCS.2022.40](https://doi.org/10.4230/LIPIcs.FSTTCS.2022.40); read as arXiv:2207.07694v3, whose numbering is used here: Section 2 (Parikh automata), Section 3 (acceptance conditions over infinite words) and Example 2.
