# Nondeterministic space s is in alternating time s²

For every time-constructible $s$,

$$
\mathsf{NSPACE}(s)\subseteq\mathsf{ATIME}\bigl((n+s(n))^2\bigr),
$$

so $\mathsf{NSPACE}(s)\subseteq\mathsf{ATIME}(O(s^2))$ when $s(n)\ge n$.

## Proof sketch

Play Savitch's midpoint game on the configuration graph: for $O(n+s)$ rounds the existential player writes a midpoint configuration of $O(n+s)$ bits and the universal player picks a half; the final single-step test of two configurations is done in quadratic time.

## Depends on

- [Alternating time and space classes ATIME, ASPACE, AP, APSPACE and AL](alternating-time-and-space-classes.md)
- [Nondeterministic space classes](../../time-and-space-complexity-classes/nspace.md)

## Proof depends on

- [Savitch's theorem: NPSPACE = PSPACE](../../savitch.md)
- [Configuration graph of a space-bounded machine](../configuration-graph-of-a-space-bounded-machine.md)

## Sources

- Ashok K. Chandra, Dexter C. Kozen and Larry J. Stockmeyer, "Alternation", Journal of the ACM 28(1), 1981.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
