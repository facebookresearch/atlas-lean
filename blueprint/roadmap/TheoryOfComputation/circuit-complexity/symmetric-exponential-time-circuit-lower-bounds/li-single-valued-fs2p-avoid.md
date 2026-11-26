# Li: a single-valued FS2P algorithm solves Avoid on every input length

There is a single-valued $\mathrm{FS}_2\mathrm{P}$ algorithm $A$ such that for every circuit $C\colon\{0,1\}^n\to\{0,1\}^{n+1}$, $A(C)$ outputs a canonical $y_C\notin\mathrm{Im}(C)$. Consequently (by Cai's theorem) there is a single-valued $\mathrm{FZPP}^{\mathrm{NP}}$ algorithm that, for every such $C$, outputs $y_C$ with probability at least $2/3$ and otherwise $\bot$.

## Proof sketch

After a stretch-amplification step to stretch $2n$, run the post-order Korten reduction against the known non-image $f$ of the GGM tree. Each prover sends a short description of the history; the verifier spot-checks local consistency with a universal quantifier over $O(\log T)$-bit vertex names. The selector compares two claimed histories: it locates a vertex where they disagree and walks down toward the leaves, whose correct values are known, to decide which prover lied; the honest history then yields $y_C$.

## Depends on

- [Single-valued FΣ2P and FS2P algorithms for search problems](single-valued-fsigma2p-and-fs2p.md)

## Proof depends on

- [Li: with post-order traversal the history of Korten's reduction has a description of size poly(n)](post-order-history-short-description.md)
- [Cai: S2P is contained in ZPP^NP](cai-s2p-subset-zpp-np.md)

## Sources

- Zeyong Li, "Symmetric Exponential Time Requires Near-Maximum Circuit Size: Simplified, Truly Uniform", STOC (2024), arXiv:2310.17762.
