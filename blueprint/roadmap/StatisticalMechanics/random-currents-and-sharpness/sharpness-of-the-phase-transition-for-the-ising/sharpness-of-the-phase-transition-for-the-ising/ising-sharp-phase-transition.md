# Sharpness of the Ising phase transition on $\mathbb{Z}^d$, $d \ge 2$

Sharpness of the phase transition for the Ising model on `ℤ^d`, `d ≥ 2`: for `β ≥ β_c`, `m*(β) ≥
√(1 - (β_c/β)²)`; for `0 ≤ β < β_c`, the plus-state two-point function `z ↦ ⟨σ_0σ_z⟩^+_β` is
summable and decays as `exp(-c‖z‖₁)`. Reference: H. Duminil-Copin, V. Tassion, "A new proof of the
sharpness of the phase transition for Bernoulli percolation and the Ising model", Comm. Math. Phys.
343 (2016) 725–745, Theorem 1.2; first proved in M. Aizenman, D. J. Barsky, R. Fernández, "The phase
transition in a general class of Ising-type models is sharp", J. Stat. Phys. 47 (1987) 343–374.
Scope: `β_c` is `Ising.betaC d`, the infimum of the inverse temperatures with positive spontaneous
magnetization, and distance is the `ℓ¹` distance (equivalent to the Euclidean one up to constants).
The statement does not include `0 < β_c < ∞`; positivity follows from `tildeBetaCIsing_pos` and the
identification `β_c = β̃_c` in the proof, finiteness from the Peierls transition.
