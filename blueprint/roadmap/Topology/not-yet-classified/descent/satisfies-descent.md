# Satisfies Descent

Stevenson's Definition 4.1: an inner fibration `p : X ⟶ S`
*satisfies descent* relative to `f : S ⟶ T` if there is an inner
fibration `q : Y ⟶ T` and a map `g : X ⟶ Y` forming a pullback
square `IsPullback g p q f`. Following the letter of the definition,
`InnerFibration p` is not part of the predicate; it follows from the
pullback square (`SSet.SatisfiesDescent.innerFibration`).
