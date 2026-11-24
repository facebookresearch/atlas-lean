# Inside eq tree Sum

The inside recurrence equals the sum of derivation weights (Collins,
Section 3): `inside d A w` is the sum of `weightOf` over valid trees of
depth at most `d` with yield `w` rooted at `A`. This is purely algebraic:
no normalization is assumed.
