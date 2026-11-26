# Nilpotent evaluation is adic evaluation

For a finite type of variables, a nilpotent
ideal `J` of the `R`-algebra `C` and a point `x` with every coordinate in `J`,
`nilpotentEval J hJ x hx f` equals the `J`-adic evaluation `MvPowerSeries.adicEval J x f`: the
ring `C` is `J`-adically complete (`IsAdicComplete.of_isNilpotent`), the point lies in `J`, hence
in the radical of `J`, and the adic sum has only the finitely many nonzero terms that
`nilpotentEval` adds up.
