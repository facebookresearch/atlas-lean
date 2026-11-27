# Coinduction Split

Let `C` have products indexed by `G` and `H × G` and have equalizers.
For an injective homomorphism `φ : H →* G` and an `H`-action `X`, this map
from the full `G`-indexed product to `coinductionCarrier φ X` reads the
input at `cosetRepresentative φ g` and applies
`(X.ρ (cosetCoordinate φ g)).asHom` to construct its coordinate at `g`.
The equation `φ (cosetCoordinate φ g) * cosetRepresentative φ g = g`
identifies the chosen representative and transport. Arbitrary coordinates
at nonrepresentative indices are reconstructed, not retained unchanged.
