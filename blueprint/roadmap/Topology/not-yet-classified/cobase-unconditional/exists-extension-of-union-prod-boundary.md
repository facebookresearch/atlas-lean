# Source-prescribed `Δ(1)`-prism extension over a cell

(packet T47(i), closing the source half of `PrismCobase.lean`
item (i)). A map out of `∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {0}` into a
quasicategory extends to the prism `Δ[n] ⊗ Δ[1]` as soon as the
image of the vertical edge at vertex `0` is an equivalence (no
hypothesis is needed for `n = 0`, where the filler is
degenerate). The proof is the downward induction along
`SSet.prismSrcFilt` of §1 of the header.
