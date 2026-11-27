# Satisfiability of word equations is in PSPACE


Whether a word equation with constants over a free monoid has a solution can be decided in polynomial space; the recompression algorithm does it nondeterministically using $O(n \log n)$ bits for an equation with $n$ symbol occurrences.

Let WordEquations be the decision problem: given a word equation $U = V$ with letters and variables, encoded as a bitstring of length $m$ in which each of the $n = |U| + |V|$ symbol occurrences is written with $O(\log n)$ bits, decide whether some substitution $\sigma$ of words over the letters of $UV$ for the variables, possibly sending variables to the empty word, satisfies $\sigma(U) = \sigma(V)$. Then:

1. there is a nondeterministic algorithm using $O(n \log n)$ bits of space that accepts exactly the satisfiable equations, and on every satisfiable equation some accepting run takes time polynomial in $n$ and $\log(N + 2)$, where $N$ is the least length $|\sigma(U)|$ of a solution;
2. since $n \le m$, WordEquations lies in $\mathrm{NSPACE}(s)$ with $s(m) = m \log (m + 2)$, measured in the input length $m$, and hence in $\mathrm{PSPACE}$.

Satisfiability does not change if solutions may use further letters, since such letters can be replaced by a fixed letter of $UV$, and an equation without letters is solved by sending every variable to the empty word. No lower bound beyond NP-hardness is known, so this is not a completeness result, and whether WordEquations lies in NP is open.


## Depends on

- [Ordinary word equation](../../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)
- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)
- [Nondeterministic space classes](../../../complexity-classes/time-and-space-complexity-classes/nspace.md)
- [Polynomial space for decision problems](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Soundness and completeness of recompression](../recompression/recompression-is-sound-and-complete.md)
- [Savitch's theorem: NPSPACE = PSPACE](../../../complexity-classes/savitch.md)

## Expansion

Guess the set of variables with empty value, delete them, and run the recompression algorithm on the resulting equation. For the guess matching a solution of least length, its restriction is a length-minimal solution of the reduced equation, of length $N$, so some run accepts after $O(\log(N + 2))$ phases of polynomial time, storing equations with $O(n)$ symbols; with the basic block compression the space is $O(n^2)$ bits. For $O(n \log n)$ bits, block compression is replaced by an improved version that never writes block lengths: it guesses which maximal blocks have equal length, writes these equalities as a small system of linear Diophantine equations in the lengths of the popped prefixes and suffixes, and checks the system's satisfiability nondeterministically within space linear in the bit size of the equation. The stored equation then has $O(n)$ letters of $O(\log n)$ bits each, and the time bound in $n$ and $\log N$ is retained. Runs exceeding the space bound or an exponential step counter are rejected. Savitch's theorem gives the deterministic polynomial-space algorithm.

The first polynomial-space algorithm was given by W. Plandowski (FOCS 1999; Journal of the ACM 51 (2004), 483–496).

This page becomes ready once the improved block compression (Jeż, Lemmas 15, 16 and 18) and the linear-space check of small linear Diophantine systems (Jeż, Lemma 12) are pages of their own.

## Sources

- Artur Jeż, "Recompression: a simple and powerful technique for word equations", arXiv:1203.3705v3 (2014), https://arxiv.org/abs/1203.3705v3; published in Journal of the ACM 63(1), Article 4 (2016), https://doi.org/10.1145/2743014; conference version STACS 2013, LIPIcs 20, 233–244, https://doi.org/10.4230/LIPIcs.STACS.2013.233, Theorem 1 and Lemmas 9–11 (Section 3); Section 4 with Lemmas 12, 15, 16 and 18 for the improved block compression and the $O(n \log n)$-bit bound, stated in the abstract and at the start of Section 5; Section 1 for the NP lower bound
- Artur Jeż, "Word Equations in Nondeterministic Linear Space", ICALP 2017, LIPIcs 80, Article 95 (2017), https://doi.org/10.4230/LIPIcs.ICALP.2017.95 (journal version: Journal of Computer and System Sciences 123 (2022), 122–142, https://doi.org/10.1016/j.jcss.2021.08.001), Section 1, which records the NP and PSPACE bounds, and Section 2, "Notions", on letters outside the equation
