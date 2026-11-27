# Infinitely-often versus almost-everywhere circuit lower bounds

A language $L$ is **not in $\mathcal{C}$ almost everywhere** (written $L \notin \mathrm{i.o.}\text{-}\mathcal{C}$) if for every family of $\mathcal{C}$-circuits $\{C_n\}$ of the given size bound, $C_n$ fails to compute $L \cap \{0,1\}^n$ for **all but finitely many** $n$. The weaker statement $L \notin \mathcal{C}$ requires failure only for **infinitely many** $n$. Lower bounds obtained by diagonalization against nondeterministic time, such as Williams's, are a priori only infinitely-often, since the nondeterministic time hierarchy is not known to hold almost everywhere.

## Sources

- L. Chen, X. Lyu, R. Williams, "Almost-everywhere circuit lower bounds from non-trivial derandomization", FOCS (2020), ECCC TR20-150.
