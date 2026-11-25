# Categorical Equivalences right of is Pullback

Categorical equivalences transport to the right side of a
descent square whose horizontal maps are categorical
equivalences: `g ≫ q = p ≫ f` is a categorical equivalence, and
cancelling `g` (two-out-of-three,
`SSet.categoricalEquivalences.hasTwoOutOfThreeProperty`) gives
`q`. This is Stevenson's "Clearly `p'` is a categorical
equivalence" in Step 0, with horizontal categorical equivalences
in practice supplied by inner anodyneness via
`SSet.categoricalEquivalences.of_innerAnodyneExtensions`.
