# Determinizability of one-counter nets is undecidable

No algorithm decides whether a one-counter net has an equivalent deterministic one-counter net, under any of the notions that fix the initial
counter, quantify over all initial counters, or allow some initial counter.

**Theorem (Almagor and Yeshurun).** For one-counter nets over a general alphabet, in the sense of
[determinization notions for one-counter nets](determinization-notions-for-one-counter-nets.md):

1. $0$-determinizability is undecidable;
2. $\forall$-determinizability is undecidable;
3. $\exists$-determinizability is undecidable.

The source leaves the decidability of uniform determinizability open (Section 6) and shows an Ackermannian lower bound for it. Over a one-letter alphabet every OCN is
$0$-, $\forall$- and $\exists$-determinizable, and uniform determinizability is decidable.

## Depends on

- [Determinization notions for one-counter nets](determinization-notions-for-one-counter-nets.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

For $0$-determinizability, the proof reduces the problem of whether the reachability set of a configuration $(\ell_0, \mathbf{0})$ of a lossy counter machine is
finite, which is undecidable (Mayr; Schnoebelen): from the machine it builds an OCN that has an equivalent DOCN from counter $0$ exactly when the reachability
set is finite. For $\forall$-determinizability, a new initial letter $\#$ either moves, with effect $0$, to the original net, or, with effect $-1$, to a universal state;
from counter $c \ge 1$ the language is $\# \Sigma'^*$, so the new net is $\forall$-determinizable exactly when the original one is $0$-determinizable. For
$\exists$-determinizability, the proof reduces the halting problem of two-counter machines using a construction from earlier work on parameterized universality of one-counter nets: from a machine it builds an OCN that, if the machine halts, accepts all words over its alphabet from some initial counter, and, if it does not halt, has for every initial counter a word after which no run accepts any word of the form $\#^*$. The proof then adapts this net into one that is $\exists$-determinizable exactly when the machine halts. A complete expansion links a page for the undecidability of finiteness of the reachability set of lossy counter machines, which items 1 and 2 start from (Lemma 3 of the source).

## Sources

- S. Almagor and A. Yeshurun, "Determinization of one-counter nets", in *33rd International Conference on Concurrency Theory (CONCUR 2022)*, LIPIcs 243, paper 18, 2022, doi:10.4230/LIPIcs.CONCUR.2022.18; read in arXiv:2112.13716v1: Lemma 3 and Theorems 7, 8 and 10 of Section 4 with their proofs, Theorem 11 (the Ackermannian lower bound for uniform determinizability), and Theorems 17 and 18 of Section 5 on a singleton alphabet, with the numbering of that version.
