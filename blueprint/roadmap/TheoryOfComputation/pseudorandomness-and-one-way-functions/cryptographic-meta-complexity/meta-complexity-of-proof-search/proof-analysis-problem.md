# The Proof Analysis Problem PAP and analyzable proof systems

For a proof system $Q$, the Proof Analysis Problem asks, given a CNF $\varphi$ and a $Q$-proof that $\varphi$ has no Resolution refutation of size $s$, whether $\varphi$ is satisfiable; $Q$ is analyzable if this is in P once $s\ge n^{c}$.

For a CNF formula $\varphi$ over $n$ variables with $m$ clauses and $s\in\mathbb{N}$, let $\mathrm{Ref}_s(\varphi)$ be the CNF whose satisfying assignments encode Resolution refutations of $\varphi$ of size $s$ (blocks of variables describing $s$ clauses, their literals and the resolution or weakening steps that derive them). For a propositional proof system $Q$,

$$
\mathrm{PAP}_Q=\{(\varphi,\pi,1^{s}) : \varphi\in\mathrm{SAT}\text{ and }\pi\text{ is a }Q\text{-proof of }\neg\mathrm{Ref}_s(\varphi)\}.
$$

$\mathrm{PAP}_Q[s(n)]$ restricts the size parameter to be at least $s(n)$. $Q$ is **analyzable** if $\mathrm{PAP}_Q[n^{c}]\in\mathsf{P}$ for some constant $c>0$. The search version $\mathrm{FPAP}_Q$ takes $(\varphi,1^{s},\pi)$ with $\pi:Q\vdash\neg\mathrm{Ref}_s(\varphi)$ and outputs a satisfying assignment of $\varphi$ if $\varphi\in\mathrm{SAT}$, and $0$ otherwise.

Basic facts: $\mathrm{PAP}_Q\in\mathsf{NP}$ for every Cook–Reckhow system $Q$; analyzability is closed downward under p-simulation; $\mathrm{PAP}_{\mathrm{Res}}[n^{2}]$ is in P-uniform $\mathsf{AC}^0$, so Resolution is analyzable; and if $Q\ge\mathrm{Res}$ is both analyzable and automatable, then $\mathsf P=\mathsf{NP}$.

## Expansion

When $\varphi$ is satisfiable it has no refutation at all, so every Resolution lower bound for it is true and the problem is well defined; the size restriction removes degenerate instances such as $s=1$, which make $\mathrm{PAP}_Q$ trivially NP-hard. Resolution is analyzable because, by the Atserias–Müller lower bound, unsatisfiable $\varphi$ make $\neg\mathrm{Ref}_{n^{2}}(\varphi)$ require exponentially long Resolution proofs, so a short Resolution proof of it certifies satisfiability. The connection with automatability: an automating algorithm would find a short proof of $\neg\mathrm{Ref}_{n^{c}}(\varphi)$ whenever $\varphi$ is satisfiable, and an analyzer would then decide satisfiability.

## Depends on

- [The Atserias–Müller reduction from SAT to resolution proof size](../../../../Logic/proof-theory/automatability-of-proof-systems/am-reduction-formula.md)
- [Automatable proof systems](../../../../Logic/proof-theory/automatability-of-proof-systems/automatable-proof-system.md)

## Proof depends on

- [Atserias–Müller: automating resolution is NP-hard](../../../../Logic/proof-theory/automatability-of-proof-systems/atserias-muller.md)

## Sources

- Noel Arteche, Albert Atserias, Susanna F. de Rezende and Erfan Khaniki, "The Proof Analysis Problem", *66th IEEE Symposium on Foundations of Computer Science (FOCS 2025)*, 2025, https://doi.org/10.1109/FOCS63196.2025.00133; numbering from arXiv:2506.16956v2 (Definitions 2.4, 3.1, 3.2 and 3.5, Remark 3.3, Propositions 3.4 and 3.6).
