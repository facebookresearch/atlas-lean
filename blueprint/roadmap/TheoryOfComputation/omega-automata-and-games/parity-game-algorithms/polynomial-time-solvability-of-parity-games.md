# Polynomial-time solvability of parity games

Can the winner of a finite [parity game](../parity-games/parity-game.md), given with its arena, owners and priorities, be decided in
polynomial time? The problem lies in NP ∩ coNP, since a positional winning strategy is a certificate that can be checked in
polynomial time, and it is solvable in quasipolynomial time.

## Depends on

- [Parity game](../parity-games/parity-game.md)

## What would settle it

An algorithm deciding the winner in time polynomial in the number of vertices and edges, for arbitrary numbers of
priorities, or a proof that none exists under a standard complexity assumption. Strong separating safety automata and universal trees
cannot give such an algorithm by themselves.

## Status

The cited sources state the question as open; this page does not certify its present status. Polynomial-time solvability is
equivalent to polynomial-time model checking of the modal $\mu$-calculus.

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Theorem 2.1 (NP ∩ coNP) and the bibliographic references of Chapter 2 on the quasipolynomial algorithms.
- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996, the discussion after Theorem 6.16 (NP ∩ coNP, the open question and its equivalence with $\mu$-calculus model checking).
- W. Czerwiński, L. Daviaud, N. Fijalkow, M. Jurdziński, R. Lazić and P. Parys, "Universal trees grow inside separating automata: quasi-polynomial lower bounds for parity games", *Proceedings of the 30th ACM-SIAM SODA*, 2019, arXiv:1807.10546v2: Section 1 and the abstract (the lower bound as a barrier).
