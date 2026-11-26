# Lifting a monotone map to higher-universe carriers

For preorders `X, Y : Type` and a monotone map `f : X →o Y`, the monotone map
`liftedCoordinates.{u} f : ULift.{u} X →o ULift.{u} Y` transports `f` through the order
isomorphisms with `X` and `Y`. It sends `x` to `ULift.up (f x.down)`.
