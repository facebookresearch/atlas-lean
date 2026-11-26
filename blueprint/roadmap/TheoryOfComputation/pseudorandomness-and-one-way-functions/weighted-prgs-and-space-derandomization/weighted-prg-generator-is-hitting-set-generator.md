# Braverman–Cohen–Garg: the generator of a weighted PRG is a hitting set generator

If $(G,\rho)$ is an $\varepsilon$-WPRG for a class $\mathcal{F}$ of Boolean functions on $n$ bits, then $G$ is an $\varepsilon'$-hitting set generator for $\mathcal{F}$ for every $\varepsilon'\gt\varepsilon$. Hence explicit WPRGs for width-$w$ length-$n$ ROBPs give explicit HSGs with the same seed length.

## Proof sketch

If $f\in\mathcal{F}$ has $f(G(y))=0$ for all seeds $y$, then the weighted estimate $\mathbb{E}_y[\rho(y)f(G(y))]$ equals $0$, so the WPRG guarantee gives $\mathbb{E}[f]\le\varepsilon\lt\varepsilon'$. Contrapositively, every $f$ with $\mathbb{E}[f]\ge\varepsilon'$ is hit.

## Depends on

- [Weighted pseudorandom generators (pseudorandom pseudodistributions)](weighted-pseudorandom-generators.md)
- [Regular and permutation ROBPs with one accept vertex, and hitting set generators](regular-permutation-robps-and-hitting-set-generators.md)

## Sources

- Mark Braverman, Gil Cohen and Sumegha Garg, "Pseudorandom Pseudo-distributions with Near-Optimal Error for Read-Once Branching Programs", STOC (2018); SIAM Journal on Computing 49(5) (2020), ECCC TR17-161.
- William M. Hoza, "Better Pseudodistributions and Derandomization for Space-Bounded Computation", APPROX/RANDOM (2021), ECCC TR21-048.
