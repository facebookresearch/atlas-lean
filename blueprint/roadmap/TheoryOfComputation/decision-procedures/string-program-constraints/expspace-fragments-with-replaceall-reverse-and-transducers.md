# EXPSPACE fragments with replaceAll, reverse and transducers

Path feasibility of loop-free string programs drops from non-elementary to EXPSPACE-complete when transducers are one-way and either functional or combined only with constant-replacement replaceAll; the second fragment stays EXPSPACE-complete with linear length and letter-count assertions.

Use the language $\mathrm{SL}$ of [two-way transducers keep path feasibility decidable](two-way-transducers-keep-path-feasibility-decidable.md) (patterns of replaceAll satisfy $\varepsilon \notin L(e)$, as required in Section 4.1 of the source), and for a set $O$ of operations write $\mathrm{SL}[O]$ for its programs using only operations of $O$ and recognisable assertions.

- $\mathrm{FT}$ denotes one-way nondeterministic finite transducers: finitely many states, an initial state, final states and transitions $(q, a, q', w)$ that read exactly one letter $a \in \Sigma$ and emit a word $w \in \Sigma^*$; the size of a transition is $|w| + 1$. Such a transducer defines the relation of pairs (input, output of an accepting run), which relates the empty input only to the empty output.
- $\mathrm{FFT}$ denotes the transducers of $\mathrm{FT}$ that define a partial function.
- $\mathrm{sreplaceAll}$ denotes the unary operations $x \mapsto \mathrm{replaceAll}_e(x, u)$ with a written constant replacement word $u$.
- A *length assertion* is $\mathrm{assert}(a_1 t_1 + \dots + a_n t_n \le d)$ with integer constants in binary and each $t_i$ an integer variable over $\mathbb{N}$, a length $|x|$, or a letter count $|x|_a$.

Then:

1. Path feasibility of $\mathrm{SL}[\circ, \mathrm{replaceAll}, \mathrm{reverse}, \mathrm{FFT}]$ is [EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md)-complete.
2. Path feasibility of $\mathrm{SL}[\circ, \mathrm{sreplaceAll}, \mathrm{reverse}, \mathrm{FT}]$ is EXPSPACE-complete.
3. Path feasibility of $\mathrm{SL}[\circ, \mathrm{sreplaceAll}, \mathrm{reverse}, \mathrm{FT}]$ extended with length assertions is EXPSPACE-complete.

Length assertions cannot be added to the first fragment: with a variable replacement, replaceAll and one length equation are [undecidable](replaceall-with-length-constraints-is-undecidable.md).

## Depends on

- [Two-way transducers keep path feasibility decidable](two-way-transducers-keep-path-feasibility-decidable.md)
- [The class EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md)

## Proof depends on

- [Straight-line transducer constraints are EXPSPACE-complete](straight-line-transducer-constraints-are-expspace-complete.md)
- [Straight-line replaceAll with regular patterns is in EXPSPACE](straight-line-replaceall-with-regular-patterns-is-in-expspace.md)
- [Savitch's theorem](../../complexity-classes/savitch.md)

## Expansion

This node still needs its proof broken down; the three parts have different proofs.

Part 1 upper bound (Proposition 5.4, Appendix B). For a partial function $f$, $\mathrm{Pre}_{R_f}(L_1 \cap L_2) = \mathrm{Pre}_{R_f}(L_1) \cap \mathrm{Pre}_{R_f}(L_2)$ (Fact 1; it fails for relations, Example 5.2). So backward propagation handles each regular constraint separately, never forming products, and keeps the constraints as conjunctive automata, a transition graph with a set of state pairs whose languages are intersected (Definition 5.3); the quantitative pre-image bounds for concatenation, reverse, functional transducers and replaceAll in this representation, together with the definedness guards of partial operations, give an exponential-space procedure. Part 1 lower bound: concatenation with functional transducers is EXPSPACE-hard (the reduction for straight-line transducer constraints), and $\mathrm{SL}[\mathrm{replaceAll}]$ with automata-given assertions is EXPSPACE-hard already with single-letter patterns (Proposition 5.5 and Appendix C, a tiling reduction over an exponentially wide corridor).

Part 2 (Theorem 5.6). Guess a disjunct of each recognisable assertion; replace each $\mathrm{replaceAll}_e(x, u)$ by an equivalent one-way transducer, constructible in exponential time; remove concatenation by splitting variables into segments as for straight-line transducer constraints, the number of segments depending only on the dependency structure; remove reverse by keeping, for each variable, either it or its reversed copy, reversing transducers (and their output words) and automata accordingly. What remains is an exponential-size acyclic conjunction of transducers and regular constraints, decided in space polynomial in its size; with the guesses of the earlier steps the procedure runs in nondeterministic exponential space, hence in exponential space by Savitch's theorem. Hardness: concatenation with one-way transducers.

Part 3 (Theorem 5.9, Appendix D). The same four steps, with each $|x|$ (and $|x|_a$) in a length assertion replaced by the sum over the segments of $x$, and by the length of its reversed copy where reverse was removed. The source then concludes by Lin and Barceló's Theorem 12, calling the transformed program polynomial-sized. Since the transformed program is concatenation-free but exponential in the original input, the expansion must instead use the polynomial-space procedure for the concatenation-free core with integer constraints (Lin and Barceló, Lemma 13 in Section 5.1.2 and the procedure of Section 5.1.3) to obtain exponential space in the original size. Hardness: as in part 2.

## Sources

- T. Chen, M. Hague, A. W. Lin, P. Rümmer and Z. Wu, "Decision procedures for path feasibility of string-manipulating programs with complex operations", Proceedings of the ACM on Programming Languages 3 (POPL), Article 49, 2019, doi:[10.1145/3290362](https://doi.org/10.1145/3290362); full version arXiv:1811.03167v1, <https://arxiv.org/abs/1811.03167v1>: Definition 2.3, Section 5 (the two fragments, sreplaceAll), Theorem 5.1, Fact 1, Example 5.2, Definition 5.3, Propositions 5.4 and 5.5, Theorem 5.6 with the four-step proof and Example 5.7, Definition 5.8, Theorem 5.9, and Appendices B–D.
- A. W. Lin and P. Barceló, "String solving with word equations and transducers: towards a logic for analysing mutation XSS", POPL 2016, pp. 123–136, doi:[10.1145/2837614.2837641](https://doi.org/10.1145/2837614.2837641); full version arXiv:1511.01633v1, <https://arxiv.org/abs/1511.01633v1>: Sections 5.1.2–5.1.3 (Lemma 13 and the polynomial-space procedure for the concatenation-free core with integer constraints).
