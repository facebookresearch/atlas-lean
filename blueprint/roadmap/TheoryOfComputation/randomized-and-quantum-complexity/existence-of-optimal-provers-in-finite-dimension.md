# Optimal provers exist in finite dimension

Fix a verifier for an $m$-message quantum interaction, with message register $\mathcal{M}$ of dimension $d_M$. Replace its initial
state and channels by a pure initial state and isometries on a private register $\mathcal{V}'$ of finite dimension $d_{V'}$ that
also holds the environments of their Stinespring dilations; this changes no acceptance probability, and $d_{V'} = d_V$ when the
verifier is given by a pure initial state and unitaries. The supremum defining the value is attained by a prover whose private
register has dimension $d_M d_{V'}$, so the value is a maximum. For $m = 0$ there are no prover channels and the value is the
verifier's acceptance probability on its initial state.

## Proof

Take any prover and dilate its channels as well, so that the global state on $\mathcal{V}' \otimes \mathcal{M} \otimes \mathcal{P}$ is
a unit vector at every step. A prover turn acts on $\mathcal{M} \otimes \mathcal{P}$ and leaves the reduced state $\rho$ on
$\mathcal{V}'$ unchanged, and the verifier's actions and final measurement depend only on the state of
$\mathcal{V}' \otimes \mathcal{M}$. Let $\mathcal{P}_0$ have dimension $d_M d_{V'}$, and suppose a prover on $\mathcal{P}_0$ has
produced the same states of $\mathcal{V}' \otimes \mathcal{M}$ so far, with current global state $u$. If the other prover's turn
produces the state $\sigma$ of $\mathcal{V}' \otimes \mathcal{M}$, then $\operatorname{Tr}_{\mathcal{M}} \sigma = \rho$ and
$\operatorname{rank} \sigma \le d_M d_{V'}$, so $\sigma$ has a purification $v \in \mathcal{V}' \otimes \mathcal{M} \otimes \mathcal{P}_0$.
Both $u$ and $v$ purify $\rho$ through $\mathcal{M} \otimes \mathcal{P}_0$, so $v = (I \otimes U) u$ for a unitary $U$ on
$\mathcal{M} \otimes \mathcal{P}_0$, which the prover on $\mathcal{P}_0$ applies. By induction it reproduces every acceptance
probability of every prover. Over this fixed dimension the prover's unitaries form a compact set on which the acceptance probability
is continuous, so the supremum is attained.

## Expansion

A good expansion adds a page for each pending prerequisite below.

- Proof prerequisite: Stinespring dilation of a channel between finite-dimensional spaces, with an environment of finite dimension.

## Depends on

- [Quantum interaction semantics](quantum-interaction-semantics.md)

## Proof depends on

- [Purification and unitary equivalence of purifications](../../QuantumInformation/quantum-foundations/purification-and-unitary-equivalence-of-purifications.md)

## Sources

- J. Watrous, *Quantum computational complexity*, arXiv:0804.3401, Section VI.1 (quantum interactive proofs; provers as channels on registers of finite dimension). Background reference. <https://arxiv.org/abs/0804.3401>
