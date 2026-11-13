# Inf-based $\beta_c$ equals $-\tfrac{1}{2}\log(1 - p_c)$ for $d \ge 2$

The public Ising critical inverse temperature `Ising.betaC d` in dimension `d ≥ 2` is
`-(1/2) log (1 - p_c(d, 2))`, the image of the FK critical point. This is the form
usable with `ising_sharp_phase_transition`, whose `β_c` is `Ising.betaC d`.
