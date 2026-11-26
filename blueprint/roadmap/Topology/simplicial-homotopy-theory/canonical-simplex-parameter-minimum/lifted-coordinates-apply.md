# Value of a lifted monotone map

For preorders `X, Y : Type`, `f : X →o Y`, and `x : ULift.{u} X`,
`liftedCoordinates f x = ULift.up (f x.down)`.
