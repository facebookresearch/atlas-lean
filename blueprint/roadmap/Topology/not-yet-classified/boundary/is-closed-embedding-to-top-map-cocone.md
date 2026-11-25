# Is Closed Embedding to Top map Cocone ι

Every leg of the realized boundary multicoequalizer cocone is a closed embedding.

Reuses the singleton/pair face closed embeddings and the right/left `homOfLE`
rewrites from `closedT1Embeddings_toTop_map_ι`, cancelling the boundary inclusion
via `Topology.IsClosedEmbedding.of_comp` with `leg ≫ boundary = face`.
