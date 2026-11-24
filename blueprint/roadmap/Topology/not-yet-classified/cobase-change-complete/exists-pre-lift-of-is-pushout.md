# Exists pre lift of is Pushout

The **gluing interface** of
`SSet.isPullback_pre_app_of_isPushout`: maps into `(ihom Y).obj C`
are exactly pairs of maps into `(ihom B).obj C` and
`(ihom X).obj C` whose restrictions to `(ihom A).obj C` agree.
At `W = Δ[0]` this is vertex gluing along the pushout (compare
the proof of
`SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration`); at
`W = Δ[1]` and `W = Δ[2]` it is the simplex-gluing step to which
TODO(T30-B) is reduced once the correction of simplices within
their homotopy classes is available.
