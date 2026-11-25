# Ioc Coordinate eq star mul self

A C0 square-root function on the same interval gives the coordinate as `star(g)*g`.

```lean
theorem iocCoordinate_eq_star_mul_self (b : ℝ) :
    ∃ g : C₀(Set.Ioc (0 : ℝ) b, ℂ), iocCoordinate b = star g * g
```
