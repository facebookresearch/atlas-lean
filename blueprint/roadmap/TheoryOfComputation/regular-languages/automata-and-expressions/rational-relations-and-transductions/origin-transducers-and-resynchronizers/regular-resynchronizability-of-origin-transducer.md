# Regular resynchronizability of origin transducers is undecidable

No algorithm decides, for two nondeterministic transducers, whether the origin semantics of the first is contained in that of the second
up to some bounded regular resynchronizer; this holds already for one-way transducers, and for equivalence.

**Theorem (Kuperberg and Martens).** Given two-way nondeterministic transducers $T_1, T_2$, it is undecidable whether $T_1 \preceq T_2$, that is, whether some bounded
regular resynchronizer $R$ satisfies $T_1 \subseteq R(T_2)$, in the sense of
[origin semantics of transducers and bounded regular resynchronizers](origin-semantics-of-transducers-and-bounded-regu.md). The problem stays
undecidable for one-way nondeterministic transducers, and also when $R$ ranges over any class of resynchronizers containing the $k$-shift
resynchronizers $\gamma(x, y) = (y \le x \le y + k)$ for all $k$. For one-way nondeterministic transducers, it is also undecidable whether
$T_1 \sim T_2$.

The relation $\preceq$ is decidable for unambiguous two-way transducers by earlier work, and for a fixed bounded resynchronizer
containment is decidable; the undecidability comes from quantifying over the resynchronizer. The same reduction shows that existence of a rational
resynchronizer is undecidable for one-way transducers $T_1, T_2$ with $[\![T_1]\!] \subseteq [\![T_2]\!]$.

## Depends on

- [Origin semantics of transducers and bounded regular resynchronizers](origin-semantics-of-transducers-and-bounded-regu.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The proof reduces the bounded-tape problem: does a deterministic Turing machine use a bounded amount of tape on the empty input? It is
undecidable by a simple reduction from the halting problem. Encoding runs of the machine as in the domino game for the Post correspondence problem,
one builds from the machine two one-way transducers $T_{\mathrm{down}}$ and $T_{\mathrm{up}}$ such that $T_{\mathrm{down}} \preceq T_{\mathrm{up}}$ holds exactly when
the machine uses bounded tape; in that case a $k$-shift resynchronizer without parameters already works, which gives the restricted versions. For
equivalence, replace $T_{\mathrm{down}}$ by $T_{\mathrm{down}} \cup T_{\mathrm{up}}$.

## Sources

- D. Kuperberg and J. Martens, "Regular resynchronizability of origin transducers is undecidable", in *45th International Symposium on Mathematical Foundations of Computer Science (MFCS 2020)*, LIPIcs 170, paper 58, 2020, doi:10.4230/LIPIcs.MFCS.2020.58; read in arXiv:2002.07558v3: Theorem 20 in Section 5 with the remark after it, Corollary 25 (1NTs and shift resynchronizers), Theorem 26 (equivalence of 1NTs), Corollary 27 (rational resynchronizers), Lemma 39 in Appendix A.7 (BoundTape), and Theorem 10 (unambiguous transducers) recalled in Section 4, with the numbering of that version.
