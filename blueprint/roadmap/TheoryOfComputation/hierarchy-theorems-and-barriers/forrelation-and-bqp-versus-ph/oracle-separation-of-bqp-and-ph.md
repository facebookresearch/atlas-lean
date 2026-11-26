# Raz-Tal: an oracle relative to which BQP is not contained in PH

There is an oracle $\mathcal{O}$ such that $\mathrm{BQP}^{\mathcal{O}} \not\subseteq \mathrm{PH}^{\mathcal{O}}$.

## Proof sketch

By the Furst-Saxe-Sipser connection, a $\mathrm{PH}$ machine with oracle queries on inputs of length $n$ corresponds to a constant-depth circuit of size $2^{\mathrm{poly}(n)}$ over the $2N = 2^{n+1}$ oracle bits. Take the oracle at each length to be either uniform or sampled from $\mathcal{D}$ (amplified by independent copies), and diagonalize against all PH machines: constant-depth circuits have advantage $\mathrm{polylog}(N)/\sqrt N$, while a single quantum query has advantage only $\Omega(1/\log N)$; running the one-query distinguisher on polylogarithmically many independent copies amplifies this to bounded error, so the separating language is decided with $\mathrm{polylog}(N)=\mathrm{poly}(n)$ queries.

## Depends on

- [The polynomial hierarchy](../../complexity-classes/time-and-space-complexity-classes/ph.md)

## Proof depends on

- [One quantum query distinguishes the Raz-Tal distribution from uniform](quantum-distinguisher-for-the-raz-tal-distribution.md)
- [Constant-depth circuits cannot distinguish the Raz-Tal distribution from uniform](constant-depth-circuits-cannot-detect-forrelation.md)
- [Baker-Gill-Solovay: oracles separate and collapse P vs NP](../relativization-and-oracle-separations/baker-gill-solovay.md)

## Sources

- Ran Raz, Avishay Tal, "Oracle separation of BQP and PH", Journal of the ACM 69(4) (2022), doi:10.1145/3530258; STOC (2019); ECCC TR18-107.
- Merrick Furst, James B. Saxe, Michael Sipser, "Parity, circuits, and the polynomial-time hierarchy", Mathematical Systems Theory 17 (1984).
