# Hoza: NL = UL

Nondeterministic logarithmic space equals unambiguous logarithmic space:

$$
\mathsf{NL}=\mathsf{UL}.
$$

That is, for every language $L\in\mathsf{NL}$ there is a nondeterministic logspace machine, all of whose branches halt in polynomial time, having exactly one accepting computation on every $x\in L$ and none on every $x\notin L$. Consequently $\mathsf{NL}\subseteq\mathsf{Mod}_k\mathsf{L}$ for every $k\ge 2$, in particular $\mathsf{NL}\subseteq\oplus\mathsf{L}$.

## Proof sketch

Reduce acceptance to reachability in a layered configuration graph. Enumerate polynomially many explicitly constructed weight assignments (derived from Justesen codes) to the edges of a subdivided graph, in seed order; for each, test by double inductive counting in logarithmic space whether minimum-weight paths are unique (min-isolation). For the first seed passing the test, decide reachability unambiguously by guessing the unique minimum-weight path and verifying minimality with the computed counts. Uniqueness of the accepting branch follows from the determinism of the seed search.

## Depends on

- [Unambiguous space classes USPACE and UL](unambiguous-space-classes.md)
- [The counting classes #L and Mod_k L](counting-logspace-classes.md)
- [The complexity class NL](../../time-and-space-complexity-classes/nl.md)

## Proof depends on

- [ST-connectivity is NL-complete](../../../completeness-other-classes/directed-s-t-connectivity/stcon-nl-complete.md)
- [Immerman–Szelepcsényi: NSPACE(s) = coNSPACE(s)](../nondeterministic-space-bounds/nspace-closed-under-complement.md)

## Sources

- William M. Hoza, "NL = UL", Electronic Colloquium on Computational Complexity, report TR26-323, 2026, Theorem 1.1.
- Klaus Reinhardt and Eric Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing 29(4), 2000.
