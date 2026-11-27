# Exists lift of is Fibrant

Extension of a map into a fibrant object across an anodyne morphism.

Given `f : A ⟶ X` with `X` fibrant (`IsFibrant X`) and an anodyne map `g : A ⟶ B`,
there exists `h : B ⟶ X` with `g ≫ h = f`. The proof fills the commutative square
with left side `g`, right side `terminal.from X` (a fibration by fibrancy),
top `f`, bottom `terminal.from B`, using `hasLeftLiftingProperty`.
