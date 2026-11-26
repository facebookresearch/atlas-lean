# Catalytic Immerman–Szelepcsényi: nondeterministic catalytic space is closed under complement

For all $s=s(n)$, $c=c(n)$ with $\log n\le s\le c\le 2^{s}$,

$$
\mathsf{coCNSPACE}[s,c]\subseteq\mathsf{CNSPACE}[O(s),O(c)].
$$

Previously this was known only under strong circuit lower bound assumptions (Buhrman–Koucký–Loff–Speelman).

## Proof sketch

Apply the oracle reduction with $\mathcal{B}=\mathrm{coN}$ to get one $\mathsf{coNSPACE}[O(s)]$ query of length $2^{O(s)}$, which by Immerman–Szelepcsényi (inductive counting, scaled to space $O(s)$) is an $\mathsf{NSPACE}[O(s)]$ query. A nondeterministic catalytic machine runs the deterministic reduction, guesses the oracle computation without touching the catalytic tape, and then runs the deterministic postprocessing, so the tape is restored on every path.

## Depends on

- [Nondeterministic, bounded-error, unbounded-error and zero-error catalytic space classes](catalytic-resource-classes.md)

## Proof depends on

- [Koucký–Mertz–Pyne–Sami: catalytic space with extra resources reduces to plain space with one oracle query](kmps-catalytic-resource-oracle-reduction.md)
- [Immerman-Szelepcsenyi theorem: NL = coNL](../../immerman-szelepcsenyi.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
- Harry Buhrman, Michal Koucký, Bruno Loff and Florian Speelman, "Catalytic Space: Non-determinism and Hierarchy", Theory of Computing Systems 62(1) (2018).
