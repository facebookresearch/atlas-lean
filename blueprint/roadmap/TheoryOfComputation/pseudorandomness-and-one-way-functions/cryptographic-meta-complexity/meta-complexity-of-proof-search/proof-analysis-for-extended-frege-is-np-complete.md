# Arteche–Atserias–de Rezende–Khaniki: the Proof Analysis Problem for Extended Frege is NP-complete

For every proof system that p-simulates Extended Frege and every polynomial size bound, the Proof Analysis Problem is NP-complete under Levin reductions: Extended Frege proves Resolution lower bounds for satisfiable formulas without revealing satisfying assignments.

1. For every constant $c\in\mathbb N$, 3SAT reduces to $\mathrm{PAP}_{\mathrm{EF}}[n^{c}]$ under polynomial-time many-one Levin reductions.
2. For every propositional proof system $Q$ that p-simulates Extended Frege and every polynomial $s(n)$, $\mathrm{PAP}_Q[s(n)]$ is NP-complete under polynomial-time many-one Levin reductions. In particular such $Q$ is not analyzable unless $\mathsf P=\mathsf{NP}$, in contrast with Resolution, whose Proof Analysis Problem is in P.

More generally, $\mathrm{PAP}_S[n^{c}]$ is NP-complete for every system $S$ that is constructively closed under modus ponens, proves that Resolution is closed under restrictions, and has P-uniform proofs $\pi_n:S\vdash\neg\mathrm{Ref}_{n^{c}}(\psi_n)$ for some P-uniform sequence of unsatisfiable formulas $\psi_n$ with $n$ variables and $\mathrm{poly}(n)$ clauses.

## Expansion

Map a 3-CNF $\varphi$ on $n$ variables to $\psi=\mathrm{Disj}(\varphi,\mathrm{PHP}_n)=\bigwedge_i(\neg y\vee C_i)\wedge\bigwedge_j(y\vee D_j)$, with a fresh switch $y$, together with a uniformly constructed EF-proof of $\neg\mathrm{Ref}_{n^{c}}(\psi)$ and size parameter $1^{n^{c}}$. The proof exists regardless of satisfiability: $S^1_2$ proves that a size-$n^{c}$ refutation of $\psi$ restricted by $y\mapsto 0$ would refute $\mathrm{PHP}_n$ in size $n^{c}$, contradicting Haken's bound as formalized by Cook and Pitassi in $\mathrm{PV}_1$, and Cook's translation turns this into polynomial-size EF proofs. If $\varphi$ is satisfiable, setting the switch to $\varphi$ satisfies $\psi$; if not, $\psi$ is unsatisfiable because $\mathrm{PHP}_n$ is. Assignments of $\varphi$ and $\psi$ map to each other directly, so the reduction is Levin. Membership in NP holds for every Cook–Reckhow system.

## Depends on

- [The Proof Analysis Problem PAP and analyzable proof systems](proof-analysis-problem.md)
- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Proof depends on

- [Arteche–Atserias–de Rezende–Khaniki: short Resolution proofs of Resolution lower bounds leak satisfying assignments](resolution-proof-analysis-is-in-fp.md)

## Sources

- Noel Arteche, Albert Atserias, Susanna F. de Rezende and Erfan Khaniki, "The Proof Analysis Problem", *66th IEEE Symposium on Foundations of Computer Science (FOCS 2025)*, 2025, https://doi.org/10.1109/FOCS63196.2025.00133; numbering from arXiv:2506.16956v2 (Theorem 1.3, Theorem 5.1, Definition 5.2, Theorem 5.3, Corollary 5.4, Theorem 5.5, Corollaries 5.6 and 5.7).
