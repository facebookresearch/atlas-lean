# Measurability from determinacy

Let `Γ` be a family of subsets of Baire space `ℕ^ℕ`,
closed under preimages by Borel maps `ℕ^ℕ → ℕ^ℕ`, all of whose members are determined. Then every
member of `Γ` is `μ`-measurable for every σ-finite Borel measure `μ` on `ℕ^ℕ`
(J. Mycielski and S. Świerczkowski, *On the Lebesgue measurability and the axiom of
determinateness*, Fund. Math. 54 (1964) 67–71; Moschovakis, *Descriptive Set Theory*, 2nd ed.,
AMS 2009, 6A.17–6A.18, with Harrington's covering game).

The proof first carries the measure from `ℕ^ℕ` to Cantor space `2^ℕ` along a Borel isomorphism (Moschovakis 6A.18). There it uses Harrington's covering game: player I plays the bits of a point and player II plays finite unions of basic open sets of rapidly decreasing measure, trying to cover I's point. The game is applied to `B = S̃ \ S`, where `S̃` is a Borel hull of `S` such that `B` contains no Borel set of positive measure; if that game is determined, `B` is null (6A.17), so `S` is measurable. Player I's payoff in that game is the complement of a Borel preimage of `S`, a set of the dual class. It is determined because the game with an extra dummy first move, whose payoff is a continuous preimage of a member of `Γ`, is determined (the shift argument of Moschovakis 6A.4).

The family of all subsets of `ℕ^ℕ` satisfies the closure hypothesis, but there the determinacy hypothesis is the axiom of determinacy, which contradicts the axiom of choice ([the axiom of determinacy contradicts choice](../non-determined-games/not-forall-determined.md)).

Any family satisfying the closure hypothesis that contains a set other than `∅` and `ℕ^ℕ` contains every Borel set. A non-trivial instance therefore needs [Martin's Borel determinacy](../borel-and-analytic-determinacy/determined-of-measurable-set-borel.md), by which the Borel sets form such a family.
