# Refl

Unconditional reflexivity: the constant homotopy from `f` to `f`.

`HomotopyRelOver.refl f A p` is the unconditional constant homotopy from `f`
to `f`; both endpoints are `f` (`ι₀ = f`, `ι₁ = f`); it is stationary at `f`
on `A`; its underlying homotopy satisfies
`(HomotopyRelOver.refl f A p).h ≫ p = fst _ _ ≫ (f ≫ p)`; it needs no
`[Fibration p]`.
