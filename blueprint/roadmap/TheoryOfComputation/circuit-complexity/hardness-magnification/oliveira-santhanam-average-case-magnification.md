# Oliveira–Santhanam: average-case formula magnification for MCSP

(1) Let $s$ be subexponentially bounded and $d \ge 1$ fixed. If for arbitrarily large $n$ every De Morgan formula on $2^n$ inputs that accepts all yes-instances of $\mathrm{MCSP}[s]$ and accepts at most $2^{2^n - n}$ truth tables in total has leaf size greater than $2^{n/d}$, then some binary NP language has no polynomial-size formulas. (2) If no nonuniform family of ternary De Morgan formula devices with $o(2^n)$ leaves solves $\mathrm{MCSP}[2^{\sqrt n}]$ with zero error, answering $?$ on at most a $1/n$ fraction of truth tables for all large $n$, then some binary NP language has no polynomial-size formulas.

## Proof sketch

As in worst-case magnification, small formulas for an NP problem on short instances would yield, by random restriction of the truth table to few sampled positions, zero-error average-case formulas of sublinear or slightly superlinear size for MCSP; the one-sided error comes from the fact that sampled inconsistency certifies a no-answer.

## Depends on

- [Zero-error average-case devices for MCSP](../minimum-circuit-size-problem/zero-error-average-case-devices-for-mcsp.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Oliveira–Santhanam: formula lower bounds for approximate MCSP above N polylog N give NP ⊄ Formula[poly]](oliveira-santhanam-formula-magnification.md)

## Sources

- I. C. Oliveira and R. Santhanam, "Hardness Magnification for Natural Problems", FOCS 2018.
