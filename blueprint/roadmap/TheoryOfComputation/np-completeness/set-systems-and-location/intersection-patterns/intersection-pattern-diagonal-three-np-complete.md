# INTERSECTION PATTERN WITH ALL DIAGONAL ENTRIES 3 is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a square matrix $A = (a_{ij})$ of natural numbers with $a_{ii} = 3$ for all $i$, decide whether there are finite sets $C_1, \dots, C_n$ with $|C_i \cap C_j| = a_{ij}$ for all $i$ and $j$.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), p. 222, problem [SP9] INTERSECTION PATTERN (comment: remains NP-complete even if all a_ii = 3; reference: [Chvátal, 1978]).
- V. Chvátal, "Recognizing intersection patterns", Annals of Discrete Mathematics 8 (1980), 249-251, doi:10.1016/S0167-5060(08)70883-5.
