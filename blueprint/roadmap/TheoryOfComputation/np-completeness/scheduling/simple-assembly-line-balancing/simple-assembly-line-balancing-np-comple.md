# SIMPLE ASSEMBLY LINE BALANCING (SALBP-1) is NP-complete

The SIMPLE ASSEMBLY LINE BALANCING (SALBP-1) decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: tasks `0, …, n - 1` with integer task times `t_j ∈ ℤ₀⁺`, precedence constraints given by a directed acyclic graph on the tasks, a cycle time `c` and a number `K` of stations. Question: can the tasks be assigned to the `K` stations `0, …, K - 1` of a line so that the total task time at every station is at most `c` and every task is at a station no earlier than the stations of its predecessors?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR1] BIN PACKING (the special case without precedence constraints).
- M. Ritt and A. M. Costa, "Improved integer programming models for simple assembly line balancing and related problems", International Transactions in Operational Research 25 (2018), 1345-1359, doi:10.1111/itor.12206 (the decision version of SALBP-1 is NP-complete, since without precedence constraints it is bin packing).
- T. S. Wee and M. J. Magazine, "Assembly line balancing as generalized bin packing", Operations Research Letters 1 (1982), 56-58, doi:10.1016/0167-6377(82)90046-3.
