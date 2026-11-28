# Equivalence of residual nominal automata is undecidable

No algorithm decides whether two given residual nominal automata accept the same language.

**Proposition.** Equivalence of [residual nominal automata](nominal-automata-and-residual-nominal-automata.md) is undecidable:
given residual nominal automata $\mathcal{A}_1, \mathcal{A}_2$, it is undecidable whether $\mathcal{L}(\mathcal{A}_1) = \mathcal{L}(\mathcal{A}_2)$.
The result also holds within the class of non-guessing automata. The proof (Proposition 5.3 of the source) reduces universality of nondeterministic nominal automata, not of residual ones, which is decidable: from $\mathcal{A}$ it builds two residual automata that are equivalent exactly when $\mathcal{L}(\mathcal{A}) = \Sigma^*$.

This contrasts with universality, which is decidable for residual nominal automata; equivalence of nondeterministic nominal
automata is undecidable as well, and the result shows that residuality does not restore decidability.

## Depends on

- [Nominal automata and residual nominal automata](nominal-automata-and-residual-nominal-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the universality problem for nondeterministic nominal automata, which is undecidable (Bojańczyk). From an
automaton $\mathcal{A} = (\Sigma, Q, I, F, \delta)$, extend the alphabet with two fresh symbols $\underline{q}$ and $q$ per state, and build two
automata: $\mathcal{A}_{\mathrm{anc}}$ adds states $\underline{q}$ with transitions $\underline{q} \xrightarrow{\underline{q}} \underline{q}$ and
$\underline{q} \xrightarrow{q} q$, making every state reachable by an anchoring word; $\mathcal{A}_\top$ adds moreover an initial accepting
state $\top$ with a loop on every letter of $\Sigma$, and drops the original initial states. Both are residual, corresponding states
accept the same languages, and $\mathcal{L}(\mathcal{A}_{\mathrm{anc}}) \cap \Sigma^* = \mathcal{L}(\mathcal{A})$ while
$\mathcal{L}(\mathcal{A}_\top) \cap \Sigma^* = \Sigma^*$. Hence $\mathcal{A}$ is universal exactly when $\mathcal{A}_{\mathrm{anc}}$ and $\mathcal{A}_\top$
are equivalent. The constructions introduce no guessing, so the argument works for non-guessing automata.

## Sources

- J. Moerman and M. Sammartino, "Residuality and learning for nondeterministic nominal automata", *Logical Methods in Computer Science* 18(1), paper 29, 2022, doi:10.46298/lmcs-18(1:29)2022; numbering of the version arXiv:1910.11666v7: Proposition 5.3 with its proof, Construction 5.2, Proposition 5.1 (universality of residual automata) and the remark after Proposition 5.4 on non-guessing automata.
