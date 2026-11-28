# Emptiness of real-time communication-bounded one-way cellular automata is undecidable

No algorithm decides whether a real-time one-way cellular automaton accepting a bounded language accepts anything, already when its cells communicate only logarithmically often per link or linearly often in total.

**Theorem.** Given a real-time $\mathrm{SC}(n)$-OCA or a real-time $\mathrm{MC}(\log n)$-OCA $\mathcal M$ (see [communication-bounded one-way cellular automata](communication-bounded-one-way-cellular-automata.md)) that accepts a bounded language, it is undecidable whether $L(\mathcal M)$ is empty. An instance is the finite description $\langle S,F,A,B,\#,b_l,b_r,\delta\rangle$ of the automaton; being real time, being communication bounded and accepting a bounded language are semantic properties of it, so this is a promise problem: no algorithm answers correctly on every automaton with these properties. The automata built in the proof have them by construction.

For the same classes the source states (Theorem 10) that finiteness, infiniteness, universality, inclusion, equivalence, regularity and context-freedom are undecidable as well, by standard techniques.

## Depends on

- [Communication-bounded one-way cellular automata](communication-bounded-one-way-cellular-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The reduction is from Hilbert's tenth problem over the nonnegative integers, as Ibarra did for reversal-bounded multicounter machines. From a polynomial $p(x_1,\dots,x_n)$ with integer coefficients the source builds bounded languages $L_1(p)$ and $L_2(p)$, whose words encode values of the variables and of the monomials of $p$ by block lengths, so that a word exists iff $2^n\cdot p$, equivalently $p$, has a root in $\mathbb N^n$. Lemmas 7 and 8 show that $L_1(p)$ is accepted by a real-time $\mathrm{SC}(n)$-OCA and $L_2(p)$ by a real-time $\mathrm{MC}(\log n)$-OCA, both effectively constructed from $p$; emptiness of these automata would decide Hilbert's tenth problem, which is undecidable because, by the DPRM theorem, every r.e. set, in particular the halting set, is Diophantine.

## Sources

- Martin Kutrib and Andreas Malcher, "Bounded Languages Meet Cellular Automata with Sparse Communication", in *Proceedings of the Eleventh International Workshop on Descriptional Complexity of Formal Systems (DCFS 2009)*, Electronic Proceedings in Theoretical Computer Science 3, 2009, pp. 163–172, doi:[10.4204/EPTCS.3.15](https://doi.org/10.4204/EPTCS.3.15); read in arXiv:0907.5128v1 ([arXiv](https://arxiv.org/abs/0907.5128v1)), whose numbering is used: Theorem 9 and its proof, Lemmas 7 and 8, and Theorem 10.
