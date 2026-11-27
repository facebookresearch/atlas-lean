# Emptiness of two-way nondeterministic Parikh automata is undecidable

A two-way Parikh automaton is a two-way nondeterministic finite automaton whose transitions add integer vectors, accepting when the final sum satisfies an existential Presburger formula; no algorithm decides whether it accepts any word, while emptiness is PSPACE-complete when each position may be visited only boundedly often.

A *two-way Parikh automaton* of dimension $d$ over $\Sigma$ is a triple $P=(A,\lambda,\psi)$ where $A$ is a two-way nondeterministic finite automaton over $\Sigma$ (with end-markers), $\lambda$ assigns a vector in $\mathbb Z^d$ to each transition, and $\psi$ is an existential Presburger formula with $d$ free variables, i.e. it defines a semilinear set. The value of a run is the sum of the vectors of its transitions, and a word is accepted if some accepting run of $A$ on it has a value satisfying $\psi$. The automaton is *$k$-visit* if every accepting run visits each position at most $k$ times, and *deterministic* if $A$ is.

**Theorem (Filiot, Guha and Mazzocchi).** The emptiness problem for two-way nondeterministic Parikh automata is undecidable (Theorem 4.1 of arXiv:1907.09362v1).

By contrast, emptiness is PSPACE-complete for deterministic and for bounded-visit two-way Parikh automata, and NP-complete for $k$-visit ones with $k$ fixed (one-way Parikh automata being the case $k=1$); two-way deterministic Parikh automata are effectively equivalent to unambiguous one-way ones, and their inclusion, universality and equivalence problems are coNEXPTIME-complete, while these problems are undecidable for one-way nondeterministic Parikh automata (Klaedtke and Rueß).

## Depends on

- [Semilinear set of vectors](../../../../context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The reduction is from solvability in $\mathbb N$ of systems of polynomial equations $p_1=p_2$ with natural coefficients (Hilbert's tenth problem). For each polynomial $p$, words over an alphabet with letters $0_x$ for the variables and $1_{p'}$ for the subpolynomials $p'$ of $p$ encode a valuation $\nu$ by the number of $0_x$'s and a value by the number of $1_p$'s. By induction on $p$, a two-way Parikh automaton accepts exactly the correct encodings: for a sum it checks the two summands in separate passes and then counts letters in fresh dimensions with a linear constraint, and for a product it makes a nondeterministically chosen number $k$ of passes, adding the number of $1_{p_2}$'s to a counter on each pass, and requires $k$ to equal the number of $1_{p_1}$'s and the counter to equal the number of $1_{p_1\times p_2}$'s. Combining the automata for both sides of each equation gives one accepting a word iff the system has a solution.

## Sources

- Emmanuel Filiot, Shibashis Guha and Nicolas Mazzocchi, "Two-Way Parikh Automata", in *39th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2019)*, LIPIcs 150, 2019, pp. 40:1–40:14, doi:[10.4230/LIPIcs.FSTTCS.2019.40](https://doi.org/10.4230/LIPIcs.FSTTCS.2019.40); read in arXiv:1907.09362v1 ([arXiv](https://arxiv.org/abs/1907.09362v1)), whose numbering is used: the introduction (contributions), Section 2 (definition of two-way Parikh automata), Theorems 4.1 and 4.3 in Section 4, and the proof of Theorem 4.1 in the appendix.
