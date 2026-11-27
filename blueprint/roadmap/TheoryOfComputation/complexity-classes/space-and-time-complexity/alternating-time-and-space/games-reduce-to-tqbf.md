# Polynomial-length games reduce to TQBF

For every game verifier as in the characterization of $\mathsf{AP}$ (polynomial number $p(n)$ of one-bit moves with a polynomial-time final predicate $V$), there is a polynomial-time map $x\mapsto\Phi_x$ to closed quantified Boolean formulas in prenex conjunctive normal form, with quantifier prefix following the move owners and auxiliary existential variables for the Cook–Levin tableau of $V$, such that $x$ is a win for the existential player iff $\Phi_x$ is true. Consequently every language in $\mathsf{AP}$ polynomial-time many-one reduces to $\mathrm{TQBF}$, and $\mathrm{TQBF}$ restricted to alternating prenex CNF formulas is $\mathsf{PSPACE}$-complete.

## Proof sketch

Encode the computation of $V$ on the moves by a CNF tableau whose auxiliary variables are quantified existentially innermost; the tableau is satisfiable for fixed moves iff $V$ accepts, so the quantified formula evaluates exactly the game.

## Depends on

- [Alternating polynomial time equals polynomial-length game verification](ap-as-polynomial-length-games.md)
- [TQBF as a decision problem](../../../completeness-other-classes/true-quantified-boolean-formulas/tqbf-dec.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)
- [Chandra–Kozen–Stockmeyer: AP = PSPACE](ap-eq-pspace.md)

## Sources

- Ashok K. Chandra, Dexter C. Kozen and Larry J. Stockmeyer, "Alternation", Journal of the ACM 28(1), 1981.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
