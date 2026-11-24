# Is Colimit of is Colimit forget of is Closed Embedding

Finite closed-gluing: a finite `TopCat` cocone is colimiting when
its image in `Type` is colimiting and each leg is a closed embedding.
The statement is the reusable packet for both realized boundary and horn
comparisons, via `nonempty_isColimit_iff_eq_coinduced` reduced to the
topology equality `c.pt.str = ⨆ coinduced` proved by closed-set
extensionality `TopologicalSpace.ext_isClosed` with
`isClosed_sup_coinduced_iff`. The forward direction is the direct
continuity preimage `hS.preimage (c.ι.app j).hom.continuous`; the
converse uses finite gluing `isClosed_of_forall_preimage_isClosed`.
Keep diagram-specific facts out of this file.
