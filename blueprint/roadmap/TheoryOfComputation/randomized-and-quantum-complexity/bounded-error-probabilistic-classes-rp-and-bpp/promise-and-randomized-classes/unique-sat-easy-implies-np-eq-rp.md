# If unique satisfiability is easy then NP = RP

If $\mathrm{UniqueSAT}$ (the promise problem of distinguishing formulas with exactly one satisfying assignment from unsatisfiable ones) is solvable in polynomial time, then $\mathsf{NP}=\mathsf{RP}$; if it is solvable in randomized polynomial time with one-sided error, the same conclusion holds.

## Proof sketch

Valiant–Vazirani maps a satisfiable formula, with probability $\Omega(1/n)$, to one with a unique satisfying assignment, and an unsatisfiable one always to an unsatisfiable one. Running the UniqueSAT algorithm and verifying the assignment found by self-reduction gives an RP algorithm for SAT after amplification.

## Depends on

- [UniqueSAT with a unary variable count as a decision problem](../../valiant-vazirani-theorem/unique-sat-dec.md)
- [The class RP](../../../complexity-classes/time-and-space-complexity-classes/rp.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Valiant-Vazirani: SAT reduces to UniqueSAT](../../valiant-vazirani-theorem/valiant-vazirani.md)

## Sources

- Leslie G. Valiant and Vijay V. Vazirani, "NP is as Easy as Detecting Unique Solutions", Theoretical Computer Science 47, 85–93, 1986.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
