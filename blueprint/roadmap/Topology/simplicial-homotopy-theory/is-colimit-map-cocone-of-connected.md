# Connected components preserve a coproduct of connected simplicial sets

Let `J : Type u`, `K : J → SSet.{u}`, and suppose that every `K j` is connected. If `c : Cofan
K` is a coproduct cofan with `hc : IsColimit c`, then `SSet.π₀Functor.mapCocone c` is a
colimit cocone in types. Its legs are the maps on connected components induced by the
coproduct inclusions.
