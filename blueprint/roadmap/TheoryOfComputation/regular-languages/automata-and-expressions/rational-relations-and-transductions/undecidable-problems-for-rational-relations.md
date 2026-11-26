# Undecidable problems for rational relations

Let $A$ and $B$ be alphabets with at least two letters each. Given rational relations $X, Y \subseteq A^* \times B^*$, as in
[rational relations and transducers](rational-relations-and-transducers.md), it is undecidable whether

1. $X \cap Y = \emptyset$;
2. $X \subseteq Y$;
3. $X = Y$;
4. $X = A^* \times B^*$;
5. $(A^* \times B^*) \setminus X$ is finite;
6. $X$ is a recognizable subset of $A^* \times B^*$.

The proofs reduce Post's correspondence problem. By contrast, it is decidable whether a given rational relation is empty and whether
it is finite, since both projections are regular languages.

## Depends on

- [Rational relations and transducers](rational-relations-and-transducers.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Sources

- J. Berstel, *Transductions and Context-Free Languages*, Teubner, 1979; electronic edition of Chapters I–IV, 2007, <http://www-igm.univ-mlv.fr/~berstel/LivreTransductions/LivreTransductions.pdf>: Theorem III.8.1 (Post's correspondence theorem), Proposition III.8.2, Lemma III.8.3 and Theorem III.8.4 with its proof.
