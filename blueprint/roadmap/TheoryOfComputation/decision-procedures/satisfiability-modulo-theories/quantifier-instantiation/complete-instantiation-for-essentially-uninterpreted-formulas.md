# Complete instantiation for essentially uninterpreted formulas

Let $F$ be an [essentially uninterpreted](essentially-uninterpreted-formulas.md) set of clauses over a background theory $T$. Then $F$ and its instantiation $F^*$ by the least solution of $\Delta_F$ are equisatisfiable modulo $T$.

1. The least solution of $\Delta_F$ is finite if and only if $\Delta_F$ is stratified.
2. Hence, for $F$ in the finite essentially uninterpreted fragment, satisfiability modulo $T$ reduces to satisfiability of the finite ground set $F^*$, which a decision procedure for ground formulas modulo $T$ decides.

The background theory $T$ is over the interpreted symbols only, so it does not constrain the uninterpreted ones. The theorem fails for the theory of all expansions of the integers by arbitrary functions, which restricts the interpretations of the uninterpreted symbols: for instance, it implies that the range of a strictly increasing function has no supremum.

**Proof.** $F^*$ consists of ground instances of $F$. Conversely, if $M$ is a model of $F^*$ and some clause $C_k$ failed in its $\pi$-extension $M^\pi$ under $\vec v$, then by [the projection lemma](relevant-domain-instantiation-preserves-ground-terms.md) it fails in $M$ under $\pi_k(\vec v)$, whose components are values of terms $r$ in the sets $S_{k,i}$, so the instance $C_k[\vec r]$ of $F^*$ fails in $M$.

## Depends on

- [Essentially uninterpreted formulas](essentially-uninterpreted-formulas.md)

## Proof depends on

- [Projection models agree with models of the instantiation](relevant-domain-instantiation-preserves-ground-terms.md)

## Sources

- Y. Ge and L. de Moura, "Complete instantiation for quantified formulas in satisfiability modulo theories", in *Computer Aided Verification (CAV 2009)*, LNCS 5643, Springer, 2009, pp. 306–320, <https://leodemoura.github.io/files/ci.pdf>, Section 3: Theorem 1 and its proof, Proposition 2 (finiteness of the least solution and stratification) and the remark on the decision procedure after it; Example 3 and the remark after it on the theory of all expansions of the integers.
