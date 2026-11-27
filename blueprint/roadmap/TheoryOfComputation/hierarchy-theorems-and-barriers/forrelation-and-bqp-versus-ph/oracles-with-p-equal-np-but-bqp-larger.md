# Oracles relative to which P = NP yet BQP escapes the polynomial hierarchy

There is an oracle relative to which $\mathrm{P} = \mathrm{NP}$ but $\mathrm{BQP} \ne \mathrm{P}$, indeed $\mathrm{P} = \mathrm{NP} \ne \mathrm{BQP} = \mathrm{P}^{\#\mathrm{P}}$; and there is an oracle relative to which $\mathrm{NP} \subseteq \mathrm{BQP}$ while $\mathrm{BQP} \not\subseteq \mathrm{PH}$.

## Proof sketch

Combine the Raz-Tal distribution with a PSPACE-complete component that collapses the polynomial hierarchy, arranged so that the collapse is computable by constant-depth circuits and therefore cannot reveal the forrelation structure. The remaining oracle bits encode a $\#\mathrm{P}$-hard function that the quantum algorithm decodes via forrelation. Random-restriction arguments handle the interaction between the two components.

## Depends on

- [The polynomial hierarchy](../../complexity-classes/time-and-space-complexity-classes/ph.md)

## Proof depends on

- [Raz-Tal: an oracle relative to which BQP is not contained in PH](oracle-separation-of-bqp-and-ph.md)
- [The polynomial hierarchy is contained in PSPACE](../../complexity-classes/polynomial-hierarchy/ph-subset-pspace.md)

## Sources

- Scott Aaronson, DeVon Ingram, William Kretschmer, "The acrobatics of BQP", CCC (2022); arXiv:2111.10409.
