# GHS susceptibility bound $\chi \le 1/h$

The GHS susceptibility bound: for `β ≥ 0` and `h > 0`, the field derivative of the magnetization
equals `β ∑_x (⟨σ_oσ_x⟩ - ⟨σ_o⟩⟨σ_x⟩)` and is at most `1/h`. Reference: R. B. Griffiths, C. A.
Hurst, S. Sherman, "Concavity of magnetization of an Ising ferromagnet in a positive external
field", J. Math. Phys. 11 (1970) 790–795. Scope: a finite graph with uniform coupling and uniform
field, the field entering the Hamiltonian as `-h ∑ σ_x` and the derivative taken in `h`; `χ ≤ 1/h`
is the weak form of the GHS consequence `χ ≤ m/h`, the full concavity statement being
`ghs_magnetization_concaveOn`. The hypotheses `β ≥ 0`, `h > 0` are satisfiable.
