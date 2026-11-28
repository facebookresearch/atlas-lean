# Parameterized realizability in token rings is undecidable

No algorithm decides whether a parameterized specification is realized, in token rings of every size, by copies of a single
process implementation, for specifications of the forms $\forall i.\ \varphi(i, i+1)$, $\forall i \neq j.\ \varphi(i, j)$ and
$\forall i \neq j.\ \varphi(i, i+1, j)$.

**Theorem.** The [parameterized realizability problem](token-rings-and-isomorphic-and-parameterized-rea.md) is undecidable for
parameterized token rings and parameterized specifications of type (b) $\forall i.\ \varphi(i, i+1)$, type (c)
$\forall i \neq j.\ \varphi(i, j)$, or type (d) $\forall i \neq j.\ \varphi(i, i+1, j)$, with $\varphi$ in LTL$\setminus$X.

For specifications of type (a), $\forall i.\ \varphi(i)$, the reduction below does not apply, since the hard specifications
relate the outputs of different processes; the source proves that parameterized realizability of type (a) specifications is
decidable, by reduction to a two-process system in which the second process has a fixed implementation.

## Depends on

- [Token rings and isomorphic and parameterized realizability](token-rings-and-isomorphic-and-parameterized-rea.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Isomorphic realizability in token rings is undecidable](isomorphic-realizability-in-token-rings-is-undec.md)

## Expansion

By the cutoff theorem of Emerson and Namjoshi, the isomorphic realizability problem for a type (b) specification in rings of up
to three processes reduces to a parameterized realizability problem of type (b), and similarly for types (c) and (d) with four
and five processes. Since isomorphic realizability in token rings is undecidable, so is parameterized realizability for these
types.

## Sources

- S. Jacobs and R. Bloem, "Parameterized synthesis", *Logical Methods in Computer Science* 10(1), paper 12, 2014, doi:10.2168/LMCS-10(1:12)2014; Theorem 3.5 of the version arXiv:1401.3588v2 with its proof, Lemma 3.6 (type (a) specifications), and Theorem 3.2 (Emerson and Namjoshi).
