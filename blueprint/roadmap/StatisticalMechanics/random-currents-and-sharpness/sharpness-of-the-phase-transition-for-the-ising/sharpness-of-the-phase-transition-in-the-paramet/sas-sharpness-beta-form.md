# Witness-set form of the sharpness of the phase transition

**Witness-set form of the sharpness of the phase transition** in the `β`-parametrization: for
`d > 0`, `J > 0` and `p_c(d) < 1`, with `p(β) = 1 - e^{-βJ}` and `β̃_c = -log(1 - p̃_c)/J`:
`p̃_c = p_c`; `β > β̃_c ↔ p(β) > p̃_c`; the one-arm probability decays exponentially when
`p(β) ∈ tildePcSet d` (some finite `S ∋ 0` has `φ_{p(β)}(S) < 1`); and `θ(p(β)) ≥ (β - β̃_c)/β`
for `β > β̃_c` (Duminil-Copin–Tassion 2016, Theorem 1.1, items 1 and 3 in the form proved there).
Decay for every `β < β̃_c` and finite susceptibility are not part of this statement; see
`StatMech.Percolation.sharp_phase_transition_pc` and `finite_susceptibility_of_lt_tildeBetaCPerco`.
