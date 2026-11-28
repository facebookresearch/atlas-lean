# Residuality of nominal automata is undecidable

No algorithm decides whether a given nondeterministic nominal automaton is residual, that is, whether each of its states accepts a
derivative of the language of the automaton.

**Proposition.** Given a nondeterministic [nominal automaton](nominal-automata-and-residual-nominal-automata.md) $\mathcal{A}$, it is
undecidable whether $\mathcal{A}$ is residual. The result also holds within the class of non-guessing automata.

So residuality, a semantic property, cannot be characterized syntactically; this is why the source values learning algorithms that
produce automata which are residual by construction. For ordinary nondeterministic finite automata checking residuality is
PSPACE-complete (Denis, Lemay and Terlutte).

## Depends on

- [Nominal automata and residual nominal automata](nominal-automata-and-residual-nominal-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the universality problem for nondeterministic nominal automata, which is undecidable. From $\mathcal{A}$ take the
anchored automaton $\mathcal{A}_{\mathrm{anc}}$ of the construction used for equivalence, extend the alphabet with two symbols $\natural$ and $\#$,
and add states $x, y$ (initial) and $z$ (final), with transitions $x \xrightarrow{\natural} z$, $x \xrightarrow{\#} x$, $y \xrightarrow{\#} y$,
$z \xrightarrow{a} z$ for $a \in \Sigma$, and $y \xrightarrow{\natural} q$ for each initial state $q$ of $\mathcal{A}$. All states except possibly $y$
accept derivatives of the language, and $y$ does exactly when $\mathcal{L}(y) = \mathcal{L}(x)$, which happens exactly when $\mathcal{A}$ is
universal (for $\mathcal{A}$ with nonempty language). So the new automaton is residual if and only if $\mathcal{A}$ is universal.

## Sources

- J. Moerman and M. Sammartino, "Residuality and learning for nondeterministic nominal automata", *Logical Methods in Computer Science* 18(1), paper 29, 2022, doi:10.46298/lmcs-18(1:29)2022; numbering of the version arXiv:1910.11666v7: Proposition 5.4 with its proof and the remark after it on non-guessing automata.
