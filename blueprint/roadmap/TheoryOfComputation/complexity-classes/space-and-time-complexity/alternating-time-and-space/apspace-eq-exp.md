# Chandra–Kozen–Stockmeyer: APSPACE = EXP

Alternating polynomial space equals deterministic exponential time:

$$
\mathsf{APSPACE}=\mathsf{EXP}=\bigcup_k \mathsf{DTIME}\bigl(2^{n^k}\bigr).
$$

## Proof sketch

$\mathsf{APSPACE}\subseteq\mathsf{EXP}$: the configuration graph has $2^{O(\mathrm{poly}(n))}$ vertices and the accepting set is computed by iterating the least-fixed-point labelling. $\mathsf{EXP}\subseteq\mathsf{APSPACE}$: the existential player claims the content of a tableau cell at a given time and position (both written in polynomially many bits); the universal player challenges one of the three cells it depends on, and the game descends to time zero.

## Depends on

- [Alternating time and space classes ATIME, ASPACE, AP, APSPACE and AL](alternating-time-and-space-classes.md)
- [The class EXP](../../time-and-space-complexity-classes/exp.md)

## Proof depends on

- [Alternating space s is contained in deterministic time 2^{O(s)}](aspace-in-dtime-exponential.md)
- [Deterministic time 2^{O(s)} is contained in alternating space s](dtime-exponential-in-aspace.md)

## Sources

- Ashok K. Chandra, Dexter C. Kozen and Larry J. Stockmeyer, "Alternation", Journal of the ACM 28(1), 1981.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
