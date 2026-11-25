# Kan Complex core of special horn filling

The reduction of Kan-ness of the core to special outer horn
filling: if a quasicategory `X` fills its special outer horns in
dimensions at least `2`, then its maximal core is a Kan complex.
Inner horns of the core are filled because the core is a
quasicategory; a `1`-dimensional outer horn of the core is filled
by the degenerate edge at its vertex; an outer horn of dimension
at least `2` in the core is an outer horn in `X` whose
distinguished edge lies in the core, hence is an equivalence, a
filler in `X` is supplied by the hypothesis, and that filler is
lifted to the core by `SSet.hasLiftingProperty_horn_core_ι`.
