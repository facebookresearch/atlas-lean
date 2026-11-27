# TWO-PROCESSOR FLOW-SHOP SCHEDULING WITH CHAIN PRECEDENCE CONSTRAINTS is NP-complete

The decision problem TWO-PROCESSOR FLOW-SHOP SCHEDULING WITH CHAIN PRECEDENCE CONSTRAINTS belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

## Sources

- J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling problems", Annals of Discrete Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X, Theorem 4(h) in the preprint, Mathematisch Centrum report BW 43/75 (1975), https://ir.cwi.nl/pub/9725 (KNAPSACK reduces to `n|2|F,tree|Cmax`; the constructed instance has the single precedence pair `J_{n-1} < J_n`, so it is a chain instance: `F2|chains|Cmax`).
- P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück, table "Flow-shop problems without preemption" (`F2|chains|Cmax`, minimal NP-hard, credited to Lenstra, Rinnooy Kan, and Brucker 1977).
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS15] FLOW-SHOP SCHEDULING, p. 241 (the parent problem; solvable in polynomial time for `m = 2` without precedence constraints).
