# Emptiness of deterministic safety and co-Büchi Parikh automata is undecidable

For Parikh automata over infinite words, nonemptiness is NP-complete under reachability and Büchi acceptance but undecidable under safety and co-Büchi acceptance, already for deterministic automata.

**Theorem.** There is no algorithm that decides, given a deterministic safety Parikh automaton, whether its language of infinite words is nonempty; and there is no algorithm that decides, given a deterministic co-Büchi Parikh automaton, whether its language is nonempty (see [Parikh automata over infinite words](parikh-automata-over-infinite-words.md)).

Nonemptiness is NP-complete for reachability and for Büchi Parikh automata (Theorem 7 of the source). Universality is coNP-complete for deterministic safety and deterministic co-Büchi Parikh automata, and undecidable for deterministic synchronous reachability, nondeterministic safety, deterministic synchronous Büchi and nondeterministic co-Büchi Parikh automata (Theorem 8).

## Depends on

- [Parikh automata over infinite words](parikh-automata-over-infinite-words.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The key step is the undecidability of the *safe word* problem: given a deterministic Parikh automaton on finite words, is there an infinite word all of whose prefixes it accepts (Lemma 3)? It is proved by reduction from nontermination of decrement-guarded two-counter machines: the input word is read as a sequence of line numbers, the vector coordinates count the increments and decrements of each counter, and the automaton accepts a prefix iff its second-to-last instruction is executed correctly, so that a safe word exists iff the machine has an infinite run. Read as a deterministic safety Parikh automaton, the same automaton accepts exactly its safe words, which gives the first claim. Read as a co-Büchi Parikh automaton, it accepts a word iff from some position on no error occurs, so its language is nonempty iff the machine fails to terminate from some configuration; this reduces the undecidable universal termination problem for decrement-guarded two-counter machines (Appendix C.1 of the source).

## Sources

- S. Guha, I. Jecker, K. Lehtinen and M. Zimmermann, "Parikh Automata over Infinite Words", in *42nd IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2022)*, Leibniz International Proceedings in Informatics 250, Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2022, article 40, doi:[10.4230/LIPIcs.FSTTCS.2022.40](https://doi.org/10.4230/LIPIcs.FSTTCS.2022.40); read as arXiv:2207.07694v3, whose numbering is used here: Theorem 7 with the proofs of its items 3 and 4 (Appendix C.1), Lemma 3 and Theorem 8.
