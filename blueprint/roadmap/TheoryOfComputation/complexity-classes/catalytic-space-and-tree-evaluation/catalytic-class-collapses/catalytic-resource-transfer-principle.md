# Ordinary and catalytic space share the same resource inclusions (Koucký–Mertz–Pyne–Sami transfer)

Let $\mathcal{B}_1,\mathcal{B}_2\in\{\bot,\mathrm{N},\mathrm{coN},\mathrm{BP},\mathrm{Pr}\}$, where $\bot$ means no additional resource, and let $s=s(n)\ge\log n$. Then

$$
\mathcal{B}_1\mathsf{SPACE}[O(s)]\subseteq\mathcal{B}_2\mathsf{SPACE}[O(s)]\iff \mathcal{B}_1\mathsf{CSPACE}[O(s),O(c)]\subseteq\mathcal{B}_2\mathsf{CSPACE}[O(s),O(c)]\ \text{for all } c \text{ with } s\le c\le 2^{s}.
$$

For example $\mathsf{NL}=\mathsf{L}$ holds iff nondeterministic and deterministic catalytic space coincide for every catalytic budget, and $\mathsf{BPL}=\mathsf{L}$ iff the same holds for bounded-error randomness.

## Proof sketch

For the forward direction, apply the oracle reduction to a $\mathcal{B}_1$ catalytic machine and replace its single $\mathcal{B}_1\mathsf{SPACE}[O(s)]$ query by a $\mathcal{B}_2\mathsf{SPACE}[O(s)]$ computation, which a $\mathcal{B}_2$ catalytic machine can run between the deterministic reduction and postprocessing. For the converse take $c=s$: a catalytic tape of length $O(s)$ can be simulated on the work tape, so the catalytic classes coincide with the ordinary ones up to constant factors.

## Depends on

- [Nondeterministic, bounded-error, unbounded-error and zero-error catalytic space classes](catalytic-resource-classes.md)

## Proof depends on

- [Koucký–Mertz–Pyne–Sami: catalytic space with extra resources reduces to plain space with one oracle query](kmps-catalytic-resource-oracle-reduction.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
