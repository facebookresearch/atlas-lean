# Regular intersection emptiness of bounded tiling and bounded PCP is undecidable

For the NP-complete problems bounded tiling and bounded Post correspondence, and for the nondeterministic logspace, NP and PSPACE machine languages, no algorithm decides whether a given finite automaton accepts some positive instance.

**Theorem (Wolf).** The [regular intersection emptiness problem](the-regular-intersection-emptiness-problem.md) $\mathrm{Int}_{\mathrm{Reg}}(P)$ is undecidable for each of the following languages $P$, with the encodings of the source, where $\diamond$ stands for the separator symbol the source writes as a dollar sign:
1. the machine languages $L_{\mathrm{NL}}$, $L_{\mathrm{NP}}$ and $L_{\mathrm{PSPACE}}$ of words $\langle M\rangle\diamond x\diamond a^n$, with $\langle M\rangle$ an encoded nondeterministic Turing machine, $x$ an input word and $n$ written in unary, such that $M$ has an accepting run on $x$ that visits at most $\log n$ tape positions, takes at most $n$ steps, or visits at most $n$ tape positions, respectively (Definition 2 and Theorem 1);
2. *bounded tiling*: words $\langle T\rangle\diamond l\diamond t\diamond r\diamond b$ with $\langle T\rangle$ an encoded tile set and each side $l, t, r, b$ a list of $n$ colors separated by $\#$, the edge coloring of an $n\times n$ square, asking for a tiling of the square extending the coloring (Definition 3 and Theorem 2), and *corridor tiling*, with only top and bottom colorings of length $n$ given, asking for a tiling of an $n\times h$ corridor for some finite height $h$, which is not bounded in advance (Definition 4 and Corollary 1);
3. *bounded PCP*: $a_1\#\cdots\#a_n\diamond b_1\#\cdots\#b_n\diamond \mathrm{bin}(K)$ with $1\le K\le n$ and the $a_i,b_i$ possibly empty words, asking for a nonempty index sequence of length at most $K$ that solves the correspondence instance, the predicate of [feasible bounded PCP instances](../../np-completeness/strings-and-puzzles/bounded-post-correspondence-problem/bounded-post-correspondence-feasible.md) (Definition 5 and Theorem 3; the source writes "a sequence of $k\le K$ indices", and with the empty sequence allowed every instance would be positive).

Each of these problems is decidable on single instances: $L_{\mathrm{NL}}$ is NL-complete; $L_{\mathrm{NP}}$, bounded tiling and bounded PCP are NP-complete; $L_{\mathrm{PSPACE}}$ and corridor tiling are PSPACE-complete.

## Depends on

- [The regular intersection emptiness problem](the-regular-intersection-emptiness-problem.md)
- [Wang tiles and valid tilings](../../undecidable-problems/wang-tiles/wang-tiles-and-valid-tilings.md)
- [Feasible BOUNDED POST CORRESPONDENCE instances](../../np-completeness/strings-and-puzzles/bounded-post-correspondence-problem/bounded-post-correspondence-feasible.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)
- [Rice's theorem for languages](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-language.md)

## Expansion

Item 1: for a Turing machine $M$ the automaton accepting $\langle M\rangle\diamond \Sigma^*\diamond a^*$ meets $L_{\mathrm{NL}}$ iff $M$ accepts some word, and non-emptiness of recursively enumerable languages is undecidable. Item 2 reuses van Emde Boas's NP-hardness construction of bounded tiling from nondeterministic Turing machines: a regular set of colorings with the encoded initial configuration of $M$ on any input at the bottom, a fixed accepting configuration at the top and white sides of every length contains a tileable instance iff $M$ accepts some input. Item 3 reduces Post's correspondence problem: the regular language $a_1\#\cdots\#a_n(\#a_n)^*\diamond b_1\#\cdots\#b_n(\#b_n)^*\diamond\{0,1\}^*$ repeats the last top and bottom entries independently and allows every bound $K$; the well-formedness of instances enforces lists of equal length and $K$ at most their length, so some member is positive iff the instance has a solution. A good expansion links pages for encoded nondeterministic Turing machines and the machine languages of item 1 with a fixed encoding, and for the source's string encodings of tiling and bounded PCP instances; the linked feasibility page states the combinatorial predicate on instances, not the string filter of item 3.

## Sources

- Petra Wolf, "From decidability to undecidability by considering regular sets of instances", *Theoretical Computer Science* 899, 2022, pp. 25–38, doi:[10.1016/j.tcs.2021.11.006](https://doi.org/10.1016/j.tcs.2021.11.006); read in arXiv:1906.08027v2 ([arXiv](https://arxiv.org/abs/1906.08027v2)), whose numbering is used (separate counters for definitions, theorems and corollaries): Definitions 2–5, Theorems 1–3 and Corollary 1 with their proofs.
