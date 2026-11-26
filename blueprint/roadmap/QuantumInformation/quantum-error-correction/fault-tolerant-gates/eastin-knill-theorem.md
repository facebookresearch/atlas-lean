# The Eastin–Knill theorem

Let $\mathcal{H} = \mathcal{H}_1 \otimes \dots \otimes \mathcal{H}_n$ be a finite-dimensional system of $n$ subsystems and
let $C \subseteq \mathcal{H}$ be a code with projector $P$ and $\dim C \ge 2$ that detects every error on a single
subsystem: $P E P \in \mathbb{C} P$ for every operator $E$ acting on one $\mathcal{H}_j$ only. Let $G$ be the group of
unitary product operators $U = U_1 \otimes \dots \otimes U_n$ that preserve the code, $(I - P) U P = 0$. Then there is a
finite set $\mathcal{F} \subseteq G$ such that every $U \in G$ satisfies $U P = e^{i\theta} F P$ for some $F \in \mathcal{F}$ and
$\theta \in \mathbb{R}$: up to a global phase, product unitaries induce only finitely many distinct operators on the code
(the scalars $e^{i\theta} I$ are themselves code-preserving product unitaries, so the phase cannot be dropped). Consequently they cannot approximate every unitary on $C$ to arbitrary
accuracy, and no such code has a universal set of [transversal](transversal-gate.md) logical gates.

Proof idea: $G$ is a closed subgroup of the compact Lie group of product unitaries, hence a Lie group; the
local-error-detection hypothesis forces the connected component of the identity to act on $C$ as scalars, so $G$ acts
through the finite group of its components, up to phase.

## Depends on

- [Transversal gate](transversal-gate.md)
- [Universal gate set](../universal-gate-sets/universal-gate-set.md)

## Proof depends on

- [Lie groups: the exponential map, closed subgroups and maximal compact subgroups](../../../RepresentationTheory/lie-and-topological-representations/lie-groups-exponential-map-and-maximal-compact-subgroups.md): the closed subgroup theorem.

## Background

- [Distance of a quantum code (lower bound)](../distance-of-a-quantum-code/has-distance-at-least.md)
- [Transversal $T$ preserves the fifteen-qubit code](../small-stabilizer-codes/transversal-t-preserves-the-fifteen-qubit-code.md)

## Sources

- B. Eastin and E. Knill, *Restrictions on transversal encoded quantum gate sets*, Phys. Rev. Lett. 102 (2009), 110502, arXiv:0811.4262, Lemmas 1–2 and Theorem 1 with its proof.
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.3 ("no code allows a universal set of transversal gates").
