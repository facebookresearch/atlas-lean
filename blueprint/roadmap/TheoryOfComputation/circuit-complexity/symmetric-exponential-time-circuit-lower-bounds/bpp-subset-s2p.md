# Russell–Sundaram and Canetti: BPP is contained in S2P

$\mathrm{BPP}\subseteq\mathrm{S}_2\mathrm{P}$. Together with the trivial inclusion this refines the Sipser–Gács–Lautemann theorem: $\mathrm{BPP}\subseteq\mathrm{S}_2\mathrm{P}\subseteq\Sigma_2\mathrm{P}\cap\Pi_2\mathrm{P}$.

## Proof sketch

Amplify the error of a $\mathrm{BPP}$ machine to $2^{-n}$ on $m$ random bits. As in Lautemann's proof, if $x\in L$ then some $m$ shifts $s_1,\dots,s_m$ cover $\{0,1\}^m$ by accepting sets, and if $x\notin L$ then some $m$ shifts cover it by rejecting sets. The yes-prover sends shifts, the no-prover sends a point $r$, and the verifier checks whether some $r\oplus s_i$ is accepting; symmetric roles handle the other direction, and a counting argument shows that a cover for the correct answer always beats every point.

## Depends on

- [Symmetric alternation: the classes S2TIME[T], S2P and S2E](symmetric-alternation-s2p-s2e.md)
- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Proof depends on

- [Sipser-Gács-Lautemann: BPP is in $\Sigma_2^p$ and $\Pi_2^p$](../../randomized-and-quantum-complexity/sipser-gacs-lautemann.md)

## Sources

- Alexander Russell and Ravi Sundaram, "Symmetric alternation captures BPP", Computational Complexity 7 (1998).
- Ran Canetti, "More on BPP and the polynomial-time hierarchy", Information Processing Letters 57 (1996).
