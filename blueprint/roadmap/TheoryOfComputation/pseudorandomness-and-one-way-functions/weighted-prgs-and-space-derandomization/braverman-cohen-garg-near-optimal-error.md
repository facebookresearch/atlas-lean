# Braverman–Cohen–Garg: weighted PRGs and hitting sets with near-optimal error dependence for ROBPs

For width-$n$, length-$n$ standard-order ROBPs and every $\varepsilon\gt 0$ there is an explicit $\varepsilon$-WPRG, and hence an explicit $\varepsilon$-HSG, with seed length

$$
\widetilde{O}\bigl(\log^2 n+\log(1/\varepsilon)\bigr),
$$

where $\widetilde{O}$ hides $\log\log$ factors. Nisan's PRG has seed length $O(\log^2 n+\log n\cdot\log(1/\varepsilon))$, so this decouples the error from the length and is the first improvement over Nisan for unrestricted ROBPs; the small-error regime $\log(1/\varepsilon)\gg\log n$ is the one used inside the Saks–Zhou derandomization.

## Proof sketch

The construction follows Nisan's recursive halving of the program but tracks, instead of a single list of pseudorandom strings, a structured family of lists whose weighted combination approximates the matrix product of transition matrices of the two halves with error decreasing geometrically in the recursion; negative weights implement correction terms of the form (approximate product minus lower-order errors). The weighted guarantee yields a hitting set by the generic WPRG-to-HSG lemma.

## Depends on

- [Weighted pseudorandom generators (pseudorandom pseudodistributions)](weighted-pseudorandom-generators.md)
- [Regular and permutation ROBPs with one accept vertex, and hitting set generators](regular-permutation-robps-and-hitting-set-generators.md)

## Proof depends on

- [Braverman–Cohen–Garg: the generator of a weighted PRG is a hitting set generator](weighted-prg-generator-is-hitting-set-generator.md)

## Sources

- Mark Braverman, Gil Cohen and Sumegha Garg, "Pseudorandom Pseudo-distributions with Near-Optimal Error for Read-Once Branching Programs", STOC (2018); SIAM Journal on Computing 49(5) (2020), ECCC TR17-161.
