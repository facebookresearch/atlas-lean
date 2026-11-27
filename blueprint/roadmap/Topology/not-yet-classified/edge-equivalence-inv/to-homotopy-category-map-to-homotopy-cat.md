# To Homotopy Category map to Homotopy Category₂ map

The two comparison functors are mutually inverse on morphisms of
the path-quotient category: mapping a morphism to `HomotopyCategory₂`
and back recovers it. This is proved by `hom_rec` induction — the
generating case is the two `homMk` compatibilities, and the
composition case is functoriality.
