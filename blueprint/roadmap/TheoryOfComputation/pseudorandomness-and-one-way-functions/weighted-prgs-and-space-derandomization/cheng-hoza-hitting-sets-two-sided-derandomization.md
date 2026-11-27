# Cheng–Hoza: logspace hitting sets for ROBPs give L = BPL, and constant-width ROBPs are estimated in space O(log^2 n + log(1/ε))

1. If there is an explicit hitting set generator with seed length $O(\log n)$ (computable in logspace) for polynomial-width ROBPs with constant threshold, then $\mathsf{L}=\mathsf{BPL}$, not merely $\mathsf{L}=\mathsf{RL}$.
2. If there are logspace hitting sets for constant-width ROBPs, then given black-box access to a constant-width ROBP $f$ one can deterministically estimate $\mathbb{E}[f]$ within $\pm\varepsilon$ in space $O(\log(n/\varepsilon))$.
3. Unconditionally, $\mathbb{E}[f]$ of a constant-width length-$n$ ROBP $f$ can be estimated within $\pm\varepsilon$ deterministically in space $O(\log^2 n+\log(1/\varepsilon))$.

They also show that a fully general hitting-set-to-PRG transformation for constant-width ROBPs over large alphabets would itself yield explicit PRGs with seed length $O(\log^{1+\alpha}n)$ for every constant $\alpha\gt 0$.

## Proof sketch

The derandomization uses the hitting set only through one-sided certificates: auxiliary branching programs derived from $f$ are built so that hitting them certifies lower bounds on transition probabilities, and combining such certificates for the program and for complementary events determines $\mathbb{E}[f]$ up to the desired accuracy. Arranging these estimates recursively over the layers keeps the space logarithmic given logspace hitting sets, and the unconditional bound instantiates the hitting sets with known constructions.

## Depends on

- [Regular and permutation ROBPs with one accept vertex, and hitting set generators](regular-permutation-robps-and-hitting-set-generators.md)

## Sources

- Kuan Cheng and William M. Hoza, "Hitting Sets Give Two-Sided Derandomization of Small Space", CCC (2020); Theory of Computing 18(21) (2022), ECCC TR20-016.
