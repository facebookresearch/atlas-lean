# TAUTOLOGY is coNP-complete

$\mathrm{TAUTOLOGY}=\{\varphi : \varphi$ a propositional formula over $\neg,\wedge,\vee$ true under every assignment$\}$ is $\mathsf{coNP}$-complete under polynomial-time many-one reductions.

## Proof sketch

Membership: a falsifying assignment is a short certificate for the complement. Hardness: $\varphi\mapsto\neg\varphi$ reduces UNSAT, which is coNP-complete, to TAUTOLOGY.

## Depends on

- [The class coNP](../../the-classes-p-np-and-conp/co-np.md)

## Proof depends on

- [UNSAT is coNP-complete](../../../completeness-other-classes/unsatisfiability/unsat-conp-complete.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Example 2.23.
- Christos H. Papadimitriou, "Computational Complexity", Addison-Wesley, 1994.
