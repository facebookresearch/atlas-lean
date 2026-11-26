# Agarwala–Mertz: bipartite matching reduces to lossy coding for NC circuits and the isolation lemma is derandomized in CL

$\mathrm{MATCH}\in\mathsf{LOSSY}[\mathsf{NC}]$. Since $\mathsf{NC}\subseteq\mathsf{LOSSY}[\mathsf{NC}]\subseteq\mathsf{ZPNC}\subseteq\mathsf{RNC}$, this strengthens the classical $\mathrm{MATCH}\in\mathsf{RNC}$ (Lovász; Karp–Upfal–Wigderson; Mulmuley–Vazirani–Vazirani) and $\mathrm{MATCH}\in\mathsf{ZPNC}$ (Karloff), and it is the first natural problem known to be in $\mathsf{LOSSY}[\mathcal{C}]$ but not known to be in $\mathcal{C}$ for a class $\mathcal{C}$ beyond $\mathsf{L}$. The same analysis gives a full deterministic implementation of the isolation lemma for matchings in $\mathsf{CLP}$: a deterministic catalytic logspace procedure either finds weights isolating the relevant minimum-weight matchings or compresses its catalytic tape.

## Proof sketch

The compressor maps a weight assignment that fails to isolate to the shorter description obtained by deleting a redundant weight, and the decompressor recomputes that weight from the two minimum-weight matchings; both are computable by $\mathsf{NC}$ circuits since they consist of determinant and shortest-path computations. A LossyCode solution is a weight assignment on which compression fails, i.e. one that isolates at every size, and from it the maximum matching is computed in $\mathsf{NC}$ by Mulmuley–Vazirani–Vazirani.

## Depends on

- [The lossy coding problem LossyCode and the classes LOSSY[C]](lossy-code-problem-and-classes.md)
- [Isolation lemma](../../../../Combinatorics/probabilistic-combinatorics/isolation-lemma.md)
- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)
- [The class NC](../../time-and-space-complexity-classes/nc.md)

## Proof depends on

- [Agarwala–Mertz: bipartite maximum matching is in polynomial-time catalytic logspace (MATCH ∈ CLP)](agarwala-mertz-bipartite-matching-in-clp.md)
- [Agarwala–Mertz: a non-isolated weight is redundant and can be erased from the catalytic tape](non-isolated-weight-is-redundant.md)

## Sources

- Aryan Agarwala and Ian Mertz, "Bipartite Matching is in Catalytic Logspace", arXiv:2504.09991 (2025), ECCC TR25-048.
- Ketan Mulmuley, Umesh V. Vazirani and Vijay V. Vazirani, "Matching is as Easy as Matrix Inversion", Combinatorica 7(1) (1987).
