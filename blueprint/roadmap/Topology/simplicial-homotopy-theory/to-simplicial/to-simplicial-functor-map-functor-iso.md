# To Simplicial Functor map Functor Iso

Functor-level postcomposition comparison for the data-to-simplicial transport.

Orientation `(toSimplicialFunctor ⋙ whiskering.obj F) ≅ (mapFunctor F ⋙ toSimplicialFunctor)`,
consistent with the objectwise `toSimplicialObject_mapObjIso`. Object components reuse
`toSimplicialObject_mapObjIso`; naturality in `X` follows from the established
`toSimplicialFunctor_map_app` / `mapFunctor_map_app` computation.
