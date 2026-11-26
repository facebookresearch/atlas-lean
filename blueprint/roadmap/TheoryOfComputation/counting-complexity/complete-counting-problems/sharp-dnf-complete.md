# #DNF is #P-complete although DNF satisfiability is easy

Counting the satisfying assignments of a DNF formula is $\#\mathsf{P}$-complete (under one-query reductions), while deciding DNF satisfiability is in $\mathsf{P}$ and the count admits an FPRAS (Karp–Luby–Madras).

## Proof sketch

For a CNF $\varphi$ on $n$ variables, $\neg\varphi$ is a DNF with $\#\neg\varphi=2^{n}-\#\varphi$, so one query and a subtraction compute $\#\mathrm{SAT}$.

## Depends on

- [Counting satisfying assignments of a CNF formula](../counting-satisfiability-sat/count-sat-fun.md)
- [The counting class $\#P$](../../complexity-classes/time-and-space-complexity-classes/sharp-p.md)
- [Number of satisfying assignments of an encoded DNF formula](../karp-luby-algorithm-for-dnf-counting/dnf-count-of.md)

## Proof depends on

- [Counting SAT is #P-complete](../counting-satisfiability-sat/count-sat-sharp-p-complete.md)
- [Karp-Luby: FPRAS for DNF counting](../karp-luby-algorithm-for-dnf-counting/karp-luby-dnf-counting.md)

## Sources

- Leslie G. Valiant, "The Complexity of Enumeration and Reliability Problems", SIAM Journal on Computing 8(3), 1979.
- Richard M. Karp, Michael Luby and Neal Madras, "Monte-Carlo Approximation Algorithms for Enumeration Problems", Journal of Algorithms 10(3), 1989.
