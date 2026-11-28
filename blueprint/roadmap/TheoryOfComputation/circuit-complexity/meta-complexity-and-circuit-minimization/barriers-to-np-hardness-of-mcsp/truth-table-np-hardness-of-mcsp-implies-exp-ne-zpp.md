# Truth-table NP-hardness of MCSP implies EXP is not ZPP

If MCSP is NP-complete under polynomial-time truth-table reductions, then $\mathrm{EXP}\ne\mathrm{ZPP}$ and $\mathrm{EXP}\ne\mathrm{NP}\cap\mathrm{SIZE}(2^{n^{\varepsilon}})$ for some $\varepsilon>0$. Even ZPP-hardness of MCSP under truth-table reductions gives $\mathrm{EXP}\ne\mathrm{ZPP}$.

A language $A$ *polynomial-time truth-table reduces* to $B$ if there are polynomial-time computable $f$ and $g$ such that $g(x)=\langle q_1,\dots,q_m\rangle$ and $A(x)=f(x,B(q_1),\dots,B(q_m))$ for every $x$.

**Theorem (Hitchcock–Pavan).**

1. If MCSP is truth-table complete for NP, then $\mathrm{EXP}\ne\mathrm{ZPP}$ and $\mathrm{EXP}\ne\mathrm{NP}\cap\mathrm{SIZE}(2^{n^{\varepsilon}})$ for some $\varepsilon>0$.
2. If MCSP is polylog-Turing complete for NP, the same two conclusions hold. Here *polylog-Turing complete* means that every language in NP reduces to MCSP by a polynomial-time Turing reduction making polylogarithmically many queries; Hitchcock and Pavan use the term without spelling it out.
3. Under *Hypothesis H* (for some $\varepsilon>0$ some tally language in NP is not solvable deterministically in time $2^{n^{\varepsilon}}$), truth-table completeness of MCSP for NP implies that E does not have circuits of size $2^{\delta n}$ for some $\delta>0$.

**Theorem (Fu).** If MCSP is ZPP-hard under polynomial-time truth-table reductions, then $\mathrm{EXP}\ne\mathrm{ZPP}$.

These extend the many-one case proved by Murray and Williams ([NP-hardness of MCSP implies EXP ≠ NP ∩ P/poly and EXP ≠ ZPP](../../minimum-circuit-size-problem/murray-williams-consequences-of-mcsp-np-hardness.md)).

## Expansion

Split on Hypothesis H. If it fails, NP contains no hard tally language while EXP does, so $\mathrm{NP}\ne\mathrm{EXP}$ and hence $\mathrm{ZPP}\ne\mathrm{EXP}$. If it holds, apply the reduction to the inputs $0^n$ of a hard tally language: the queries form a sequence produced from $0^n$ in polynomial time, so they cannot all be easy instances, and an honest-reduction argument extracts truth tables of circuit complexity $2^{\delta n}$ computable in E. By the infinitely-often form of the Impagliazzo–Wigderson theorem, that lower bound derandomizes ZPP to P at infinitely many lengths, so again $\mathrm{EXP}\ne\mathrm{ZPP}$.


Expanding this node to full proof readiness requires planned proof-prerequisite pages for:

- Infinitely-often Impagliazzo–Wigderson derandomization (Hitchcock–Pavan, proof of Corollary 4.2)

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [The class EXP](../../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [ZPP](../../../complexity-classes/time-and-space-complexity-classes/zpp.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The class E](../../../complexity-classes/time-and-space-complexity-classes/e.md)
- [Polynomial-time Turing (Cook) reduction](../../../randomized-and-quantum-complexity/interactive-proofs/closure-of-ip-under-reductions/polynomial-time-turing-reduction.md)

## Proof depends on

None.

## Sources

- John Matthew Hitchcock, A. Pavan, "On the NP-Completeness of the Minimum Circuit Size Problem", *Foundations of Software Technology and Theoretical Computer Science (FSTTCS)*, 2015, https://doi.org/10.4230/LIPIcs.FSTTCS.2015.236 (Definition 2.5, Corollary 4.2 and its proof, Theorem 4.3, Corollary 4.4, Theorem 4.5).
- Bin Fu, "Hardness of Sparse Sets and Minimal Circuit Size Problem", *International Computing and Combinatorics Conference (COCOON)*, 2020, https://doi.org/10.1007/978-3-030-58150-3_39, arXiv:2003.00669v2 (Corollary 21).
