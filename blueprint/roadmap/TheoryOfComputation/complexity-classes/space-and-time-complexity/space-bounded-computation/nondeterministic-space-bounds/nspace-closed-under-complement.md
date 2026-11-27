# Immerman–Szelepcsényi: NSPACE(s) = coNSPACE(s)

For every $s$ with $\log_2 n\le s(n)$, nondeterministic space is closed under complement:

$$
\mathsf{NSPACE}(s)=\mathsf{coNSPACE}(s),
$$

where the machines use at most $c_1 s(n)+c_2$ work cells along every computation prefix and every branch halts. No space-constructibility is assumed.

## Proof sketch

Inductive counting: a nondeterministic machine computes the exact number $r_k$ of configurations reachable within $k$ steps from $r_{k-1}$, by re-guessing for each candidate configuration a path from every one of $r_{k-1}$ verified configurations. With the final count $r$ it certifies non-acceptance by exhibiting $r$ reachable non-accepting configurations. All counters are $O(s)$ bits; the unknown width is handled by counting configurations of growing width until no wider configuration appears.

## Depends on

- [Nondeterministic space classes](../../../time-and-space-complexity-classes/nspace.md)

## Proof depends on

- [Configuration graph of a space-bounded machine](../../configuration-graph-of-a-space-bounded-machine.md)
- [Immerman-Szelepcsenyi theorem: NL = coNL](../../../immerman-szelepcsenyi.md)

## Sources

- Neil Immerman, "Nondeterministic Space Is Closed under Complementation", SIAM Journal on Computing 17(5), 1988.
- Róbert Szelepcsényi, "The Method of Forcing for Nondeterministic Automata", Bulletin of the European Association for Theoretical Computer Science 33, 1987.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
