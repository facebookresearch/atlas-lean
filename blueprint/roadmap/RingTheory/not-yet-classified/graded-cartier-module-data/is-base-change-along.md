# Basis-preserving semilinear map along a ring map

For `φ : B →+* B'`,
data `D` over `B` with coefficient map `j` and `D'` over `B'` with coefficient
map `φ.comp j`: an additive map `f : D.M →+ D'.M` with
`f (w • x) = WittVector.map φ w • f x` that commutes with `F`, `V` and `ϖ`, maps
`piece i` of `D` into `piece i` of `D'`, and sends some homogeneous `V`-basis of
`D` to a homogeneous `V`-basis of `D'`. This is weaker than base change along
`φ`, the completed extension of scalars, which along the identity is an
isomorphism: if `D` has a homogeneous `V`-basis and `T` is a nonzero datum on
which `V` is bijective, the inclusion of `D` into `D × T` satisfies it along the
identity but is not surjective. As the target is indexed by `φ.comp j`, `f`
intertwines the Teichmüller actions (`IsBaseChangeAlong.map_teichmullerAct`).
