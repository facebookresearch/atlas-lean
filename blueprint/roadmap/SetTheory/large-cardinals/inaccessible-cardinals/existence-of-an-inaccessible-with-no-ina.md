# Existence of an inaccessible with no inaccessibles below it

If any inaccessible exists, some inaccessible has no inaccessibles below it:
minimize over the initial ordinals of inaccessible cardinals
(`WellFounded.has_min`), and any member of `inaccessibleBelow` would give a
smaller one.

In particular the least inaccessible — if one exists — is neither Mahlo (see
`exists_isInaccessible_not_isMahlo` in `Mahlo.lean`) nor an inaccessible fixed
point (`not_isInaccessibleFixedPoint_of_inaccessibleBelow_eq_empty` above).

## Sources

- If any inaccessible cardinal exists, some inaccessible has no inaccessibles below it.
