# Evaluation of a power series at a point of a nilpotent ideal

Let `σ` be a finite type of
variables, `J` a nilpotent ideal of the `R`-algebra `C`, and `x : σ → C` a point with every
coordinate `x s` in `J`. Choose `N` with `J ^ N = ⊥`; every monomial of total degree at least `N`
then vanishes at `x`. The value `nilpotentEval J hJ x hx f` is the finite sum of
`algebraMap R C (coeff d f) * ∏ s, x s ^ d s` over the monomials `d` of total degree below `N`.
It does not depend on the choice of `N` (`MvPowerSeries.nilpotentEval_eq_sum`), it equals the
adic evaluation `MvPowerSeries.adicEval J x f` (`MvPowerSeries.nilpotentEval_eq_adicEval`), and
it is the underlying function of the algebra homomorphism `MvPowerSeries.nilpotentEvalAlgHom`.
