# Nilpotent evaluation as an algebra homomorphism

For a finite type of variables `σ`, a
nilpotent ideal `J` of the `R`-algebra `C` and a point `x` with every coordinate in `J`,
evaluation at `x` is an `R`-algebra homomorphism `MvPowerSeries σ R →ₐ[R] C`. It is the
specialization of `MvPowerSeries.adicEvalAlgHom` to the nilpotent ideal `J`, at which `C` is
adically complete (`IsAdicComplete.of_isNilpotent`), and its underlying function is
`nilpotentEval J hJ x hx` (`MvPowerSeries.coe_nilpotentEvalAlgHom`).
