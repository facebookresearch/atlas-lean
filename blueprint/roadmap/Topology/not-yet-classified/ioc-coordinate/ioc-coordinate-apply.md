# Ioc Coordinate apply

The C0 coordinate has exactly the original real coordinate, embedded in the complex numbers.

```lean
theorem iocCoordinate_apply (b : ℝ) (x : Set.Ioc (0 : ℝ) b) :
    iocCoordinate b x = ((x : ℝ) : ℂ)
```
