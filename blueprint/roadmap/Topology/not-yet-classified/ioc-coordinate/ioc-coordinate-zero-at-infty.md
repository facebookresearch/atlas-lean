# Ioc Coordinate zero at infty

The coordinate tends to zero along the cocompact filter of `(0,b]`.

```lean
theorem iocCoordinate_zero_at_infty (b : ℝ) :
    Tendsto (fun x : Set.Ioc (0 : ℝ) b => ((x : ℝ) : ℂ))
      (cocompact (Set.Ioc (0 : ℝ) b)) (nhds 0)
```
