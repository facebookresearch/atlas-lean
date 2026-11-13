# Inf-based and sup-based Ising critical points agree for $d \ge 2$

Bridge between the two critical-point definitions: the public
`Ising.betaC d = sInf {β ≥ 0 | m*(β) > 0}` equals the sup-based
`IsingFK.betaC (magnetization d) = sSup {β > 0 | m*(β) = 0}` in dimension `d ≥ 2`.
The `β = 0` case is not covered by the phase-transition statement (which only speaks
about `β > 0`), so it is settled separately: `φ_0({0}) = tanh 0 * … = 0 < 1`, hence
the plus-state two-point function at `β = 0` is summable, hence `m*(0) = 0`.
