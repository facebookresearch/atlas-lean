# Davis's perfect set theorem from determinacy

Let `Γ` be a family of subsets of Baire
space `ℕ^ℕ`, closed under preimages by Borel maps `ℕ^ℕ → ℕ^ℕ`, all of whose members are
determined. Then every member of `Γ` is countable or contains a non-empty perfect set
(M. Davis, *Infinite games of perfect information*, Ann. of Math. Stud. 52 (1964); Moschovakis,
*Descriptive Set Theory*, 2nd ed., AMS 2009, 6A.10–6A.12; Woodin, *The continuum hypothesis,
Part I*, Notices AMS 48 (2001)).

The proof first carries the set from `ℕ^ℕ` to Cantor space `2^ℕ` along a Borel isomorphism (Moschovakis 6A.12). There it uses Davis's `*`-game, in which player I plays non-empty finite binary sequences and player II single bits: player I has a winning strategy only if the set contains a non-empty perfect set, and player II only if the set is countable (Moschovakis 6A.10–6A.11). The payoff set of this game is a Borel preimage of the given set, so the hypothesis makes the game determined. If the image in `2^ℕ` is countable, so is the set. If it contains a non-empty perfect set, the preimage of that perfect set is an uncountable Borel subset of the given set, and every uncountable Borel set contains a non-empty perfect set (6A.12).

The family of all subsets of `ℕ^ℕ` satisfies the closure hypothesis, but there the determinacy hypothesis is the axiom of determinacy, which contradicts the axiom of choice ([the axiom of determinacy contradicts choice](../non-determined-games/not-forall-determined.md)).

Any family satisfying the closure hypothesis that contains a set other than `∅` and `ℕ^ℕ` contains every Borel set. A non-trivial instance therefore needs [Martin's Borel determinacy](../borel-and-analytic-determinacy/determined-of-measurable-set-borel.md), by which the Borel sets form such a family.
