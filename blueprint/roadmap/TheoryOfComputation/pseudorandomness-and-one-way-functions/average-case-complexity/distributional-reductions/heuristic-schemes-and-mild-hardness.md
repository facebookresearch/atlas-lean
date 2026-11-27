# Heuristic schemes defeat mild average-case hardness

If $(L,\mathcal{U})\in\mathsf{HeurP}$ for the uniform ensemble $\mathcal{U}$, then for every positive polynomial $p$ there is a deterministic polynomial-time algorithm agreeing with $L$ on more than a $1-1/p(n)$ fraction of inputs of each length $n$; hence the characteristic function of $L$ is not mildly hard on average against deterministic polynomial-time heuristics.

## Proof sketch

Run the heuristic scheme with error parameter $\delta=1/(2p(n))$; its failure set has uniform measure at most $\delta$ at every length.

## Depends on

- [Distributional problems, DistNP, AvgP and HeurP](../distributional-problems.md)

## Sources

- Andrej Bogdanov and Luca Trevisan, "Average-Case Complexity", Foundations and Trends in Theoretical Computer Science 2(1), arXiv:cs/0606037, 2006.
- Shai Ben-David, Benny Chor, Oded Goldreich and Michael Luby, "On the Theory of Average Case Complexity", Journal of Computer and System Sciences 44(2), 1992.
