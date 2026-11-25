# Normal ideal on a cardinal

Let κ be a cardinal, identified with
κ = Iio(κ.ord) = {α : Ordinal ∣ α < κ.ord},
and let I⊆𝒫(κ).

I is *normal* if it is closed under diagonal unions: for every
κ-sequence ⟨ A_ξ : ξ<κ⟩ with A_ξ∈ I,

∇_{ξ<κ} A_ξ := {α<κ ∣ ∃ ξ<α, α∈ A_ξ} ∈ I.

Formally,

∀ A : κ → 𝒫(κ),  (∀ ξ, A_ξ∈ I) →
  {α∈κ ∣ ∃ ξ∈κ, ξ<α ∧ α∈ A_ξ}∈ I.
