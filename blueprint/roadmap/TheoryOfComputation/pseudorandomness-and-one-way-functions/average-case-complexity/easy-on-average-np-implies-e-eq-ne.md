# Ben-David–Chor–Goldreich–Luby: easy-on-average DistNP implies E = NE

Here $\mathsf{E}=\mathsf{DTIME}(2^{O(n)})$ and $\mathsf{NE}=\mathsf{NTIME}(2^{O(n)})$. If $\mathsf{DistNP}\subseteq\mathsf{AvgP}$, then $\mathsf{NE}=\mathsf{E}$ (Ben-David–Chor–Goldreich–Luby, Theorem 5, in contrapositive form).

## Proof sketch

By Book's characterization, $\mathsf{NE}\ne\mathsf{E}$ iff some unary language $L\in\mathsf{NP}$ is not in $\mathsf{P}$; and a unary language is in $\mathsf{P}$ iff it is decided in time polynomial on average with respect to the distribution $\mu(1^n)\propto n^{-2}$ on unary strings (Proposition 1). So $(L,\mu)\in\mathsf{DistNP}\setminus\mathsf{AvgP}$.

Derived strengthening (not stated in the cited source): with ensembles $D_n$ supported on $\{0,1\}^n$, the same conclusion follows from the weaker hypothesis $\mathsf{DistNP}\subseteq\mathsf{HeurP}$. For $L\in\mathsf{NE}$, the padded language $L'=\{x\,1^{2^{|x|}} : x\in L\}$ is in $\mathsf{NP}$. Under the polynomial-time computable ensemble that is uniform on the $2^{\ell}$ padded instances of length $N=\ell+2^{\ell}$ (and a point mass at other lengths), a heuristic scheme with error parameter $\delta=2^{-\ell-1}$ must be correct on every padded instance, since each has probability $2^{-\ell}>\delta$ (an errorless scheme is a special case); running it decides $L$ in time $\mathrm{poly}(N)=2^{O(|x|)}$.

## Depends on

- [Distributional problems, DistNP, AvgP and HeurP](distributional-problems.md)
- [The class E](../../complexity-classes/time-and-space-complexity-classes/e.md)
- [Nondeterministic time classes](../../complexity-classes/time-and-space-complexity-classes/ntime.md)

## Proof depends on

- [Hartmanis–Immerman–Sewelson: easy tally NP sets collapse NEXP to EXP](../../hierarchy-theorems-and-barriers/refined-time-hierarchies-and-padding/tally-np-collapses-nexp.md)

## Sources

- Shai Ben-David, Benny Chor, Oded Goldreich and Michael Luby, "On the Theory of Average Case Complexity", Journal of Computer and System Sciences 44(2), 193–219, 1992, Theorem 5 and Proposition 1 (via Book's characterization of $\mathsf{NE}\ne\mathsf{E}$ by unary $\mathsf{NP}\setminus\mathsf{P}$ languages); author's copy on the Weizmann homepage of O. Goldreich ("Draft from 1989, minor corrections 1997"), Section 5.1, same numbering.
