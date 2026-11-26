# Unions of stably infinite theories are stably infinite

If $T_1$ and $T_2$ are signature-disjoint first-order theories over countable signatures that are [stably infinite](convex-theories.md), then $T_1 \cup T_2$ is stably infinite. Hence Nelson–Oppen combination can be iterated over more than two component theories.

**Proof.** A satisfiable existentially quantified conjunction over the union reaches, after purification and a choice of arrangement, a pair of component conjunctions, each with an infinite model of its theory. Over a countable signature each of these has a countably infinite model, by the downward Löwenheim–Skolem theorem applied to the theory together with the conjunction, its variables read as new constants; the amalgamation of the two countably infinite models is a countably infinite model of the union.

## Depends on

- [Convex theories](convex-theories.md)

## Proof depends on

- [Nelson–Oppen combination of decision procedures](nelsonoppen-combination-of-decision-procedures.md)
- [Purification into separate form](purification-into-separate-form.md)
- [Downward Löwenheim–Skolem theorem](../../../Logic/model-theory/downward-lowenheim-skolem-theorem.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 1.11, Lemma 1.5 (amalgamation lemma), p. 26, and Theorem 1.11 with its proof, p. 31, where stable infiniteness asks for countably infinite models; the restriction to countable signatures and the downward Löwenheim–Skolem step are written out here.
