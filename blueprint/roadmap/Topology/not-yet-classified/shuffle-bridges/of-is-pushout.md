# Prism extension is stable under cobase change:

`PrismOneExtensionAt κ i C` implies
`PrismOneExtensionAt κ j C` for the cobase change `j` of `i`.
Restrict the data to `i`, extend there, glue the two prisms
along the tensored pushout, glue the sections by
`IsPushout.hom_ext`, and read verticals off the pieces at
vertices coming from either side.
