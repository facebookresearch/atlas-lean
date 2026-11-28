# Parikh automata over infinite words

A Parikh automaton is a finite automaton whose transitions also carry vectors of natural numbers; over infinite words, a run is accepting when accepting states and prefix sums in a semilinear set occur together according to a safety, reachability, Büchi or co-Büchi condition.

**Definition.** Let $\Sigma$ be a finite alphabet, $d \ge 1$ and $D \subseteq \mathbb N^d$ finite. A *Parikh automaton* (PA) is a pair $(\mathcal A, C)$ where $\mathcal A = (Q, \Sigma \times D, q_I, \Delta, F)$ is a nondeterministic finite automaton over $\Sigma \times D$ and $C \subseteq \mathbb N^d$ is [semilinear](../../../context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md). As an input, the vectors are written in binary and $C$ is given as a finite union of linear sets $\{\vec v_0+c_1\vec v_1+\cdots+c_k\vec v_k : c_i\in\mathbb N\}$, each by the list $(\vec v_0,\dots,\vec v_k)$. It is *deterministic* if for each state $q$ and letter $a \in \Sigma$ there is at most one pair $(q', \vec v)$ with $(q, (a, \vec v), q') \in \Delta$. An infinite run $(q_0, w_0, q_1)(q_1, w_1, q_2) \cdots$ of $\mathcal A$ with $q_0 = q_I$ processes the projection to $\Sigma$ of $w_0 w_1 \cdots$; write $\Phi_n$ for the sum of the vectors of $w_0 \cdots w_{n-1}$, so $\Phi_0 = \vec 0$ for the empty prefix. The run is

- *safety accepting* if $\Phi_n \in C$ and $q_n \in F$ for all $n \ge 0$;
- *synchronous reachability accepting* if $\Phi_n \in C$ and $q_n \in F$ for some $n \ge 0$;
- *asynchronous reachability accepting* if $\Phi_n \in C$ for some $n \ge 0$ and $q_{n'} \in F$ for some $n' \ge 0$;
- *synchronous Büchi accepting* if $\Phi_n \in C$ and $q_n \in F$ for infinitely many $n$;
- *asynchronous Büchi accepting* if $\Phi_n \in C$ for infinitely many $n$ and $q_{n'} \in F$ for infinitely many $n'$;
- *co-Büchi accepting* if there is $n_0$ with $\Phi_n \in C$ and $q_n \in F$ for all $n > n_0$.

The corresponding automata are safety (SPA), synchronous and asynchronous reachability (sRPA, aRPA), synchronous and asynchronous Büchi (sBPA, aBPA) and co-Büchi (CPA) Parikh automata, each accepting the infinite words over $\Sigma$ processed by an accepting run.

## Depends on

- [Semilinear set of vectors](../../../context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md)

## Proof depends on

None.

## Expansion

All these acceptance conditions are conjunctive: acceptance needs accepting states and prefix sums in $C$ together; a disjunctive variant is equivalent, since whether a prefix ends in an accepting state can be recorded in the vectors and folded into $C$. For example (Example 2 of the source), take a one-state automaton with that state accepting, counting $a$ and $b$ in two coordinates, with $C = \{(n, n) : n \in \mathbb N\}$ or its complement $\bar C$. As reachability automata, both accept every infinite word over $\{a, b\}$, since the empty prefix is balanced and every odd-length prefix is unbalanced; as safety automata, both accept no word, for the same reason.

## Sources

- S. Guha, I. Jecker, K. Lehtinen and M. Zimmermann, "Parikh Automata over Infinite Words", in *42nd IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2022)*, Leibniz International Proceedings in Informatics 250, Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2022, article 40, doi:[10.4230/LIPIcs.FSTTCS.2022.40](https://doi.org/10.4230/LIPIcs.FSTTCS.2022.40); read as arXiv:2207.07694v3, whose numbering is used here: Section 2 (Parikh automata), Section 3 (acceptance conditions over infinite words) and Example 2; the published version, open access at <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSTTCS.2022.40>, writes $d \geqslant 1$ and $n \geqslant 0$ in these definitions and numbers the example as Example 4.
