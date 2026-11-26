# Exact weighted CSP counting is #P-hard already for exactly-one constraints

Computing the partition function of Boolean CSP instances with the exactly-one weighting is $\#\mathsf{P}$-hard, even when every variable occurs in exactly two constraints. Hence exact computation of partition functions of weighted CSPs is $\#\mathsf{P}$-hard in general, while bounded treewidth makes it polynomial.

## Proof sketch

The permanent of a $0/1$ matrix, which is $\#\mathsf{P}$-complete by Valiant's theorem, is the exactly-one partition function of the row/column instance, in which each entry-variable lies in one row and one column constraint.

## Depends on

- [Partition function of a weighted CSP](partition-function-of-a-weighted-csp.md)
- [The permanent is #P-complete (Valiant)](../complexity-of-the-permanent/permanent-sharp-p-complete.md)

## Proof depends on

- [Exactly-one partition functions count perfect matchings and permanents](exactly-one-partition-function-permanent.md)

## Sources

- L. G. Valiant, "The Complexity of Computing the Permanent", Theoretical Computer Science 8(2), 189–201, 1979.
