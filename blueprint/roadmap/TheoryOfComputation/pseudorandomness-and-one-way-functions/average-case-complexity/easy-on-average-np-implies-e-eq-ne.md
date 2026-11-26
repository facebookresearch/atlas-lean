# Ben-David–Chor–Goldreich–Luby: easy-on-average DistNP implies E = NE

If every distributional problem in $\mathsf{DistNP}$ has a polynomial-time heuristic scheme (i.e. $\mathsf{DistNP}\subseteq\mathsf{HeurP}$), then $\mathsf{NE}=\mathsf{E}$.

## Proof sketch

For $L\in\mathsf{NE}$, the padded language $L'=\{x\,1^{2^{|x|}} : x\in L\}$ is in $\mathsf{NP}$. Under the ensemble that, at each padded length $N\approx 2^{|x|}$, gives every padded instance probability about $1/N$, a heuristic scheme with error parameter below $1/(2N)$ must be correct on every padded instance; running it decides $L$ in time $\mathrm{poly}(N)=2^{O(|x|)}$.

## Depends on

- [Distributional problems, DistNP, AvgP and HeurP](distributional-problems.md)
- [The class E](../../complexity-classes/time-and-space-complexity-classes/e.md)

## Proof depends on

- [Hartmanis–Immerman–Sewelson: easy tally NP sets collapse NEXP to EXP](../../hierarchy-theorems-and-barriers/refined-time-hierarchies-and-padding/tally-np-collapses-nexp.md)

## Sources

- Shai Ben-David, Benny Chor, Oded Goldreich and Michael Luby, "On the Theory of Average Case Complexity", Journal of Computer and System Sciences 44(2), 1992.
