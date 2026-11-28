# Canonical `L`-map

A Cartier `L`-map `L` on `D`, over `B` with
coefficient map `j`, that forms a commuting square with a Cartier `L`-map over a
`p`-torsion-free ring mapping onto `B`. That is, there are a commutative ring
`S` on which multiplication by `p` is injective, a ring map `jS : Zp2 p →+* S`,
a surjective ring map `φ : S →+* B`, a special Cartier module `Dl` over `S`
with coefficient map `jS`, an additive map `f : Dl.M →+ D.M` with
`IsBaseChangeAlong' φ Dl D f` (so `j = φ.comp jS`), and a Cartier `L`-map `Ll`
on `Dl`, such that `L (f x) = nMap f (Ll x)` for every `x` in `Dl.M`, where
`nMap f` is the map of `N`-modules that `f` induces. The map `f` is a
basis-preserving semilinear map along `φ`, not necessarily the base change of
`Dl` along `φ`. A special Cartier module over such an `S` is not enough: `L`
itself must satisfy this equation.
