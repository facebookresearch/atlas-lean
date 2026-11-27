# Exact weighted CSP counting is #P-hard already for exactly-one constraints

Computing the partition function of Boolean CSP instances with the exactly-one weighting is $\#\mathsf{P}$-hard, even when every variable occurs in exactly two constraints. Hence exact computation of partition functions of weighted CSPs is $\#\mathsf{P}$-hard in general, while bounded treewidth makes it polynomial.

## Proof sketch

The permanent of a $0/1$ matrix, which is $\#\mathsf{P}$-complete by Valiant's theorem, is the exactly-one partition function of the row/column instance, in which each entry-variable lies in one row and one column constraint. For bounded treewidth, the counting dynamic program over a nice tree decomposition, with each table entry a sum of products of constraint weights instead of a count of satisfying extensions, computes the partition function with polynomially many arithmetic operations.

## Depends on

- [Partition function of a weighted CSP](partition-function-of-a-weighted-csp.md)
- [The permanent is #P-complete (Valiant)](../complexity-of-the-permanent/permanent-sharp-p-complete.md)

## Proof depends on

- [Counting and deciding finite-domain CSPs over bounded treewidth](../../../ComputerScience/dynamic-programming/tree-decomposition-dynamic-programming/csp-bounded-treewidth-dynamic-programming.md)
- [Exactly-one partition functions count perfect matchings and permanents](exactly-one-partition-function-permanent.md)

## Sources

- L. G. Valiant, "The Complexity of Computing the Permanent", Theoretical Computer Science 8(2), 189–201, 1979.
- M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, Parameterized Algorithms, Springer, 2015.
