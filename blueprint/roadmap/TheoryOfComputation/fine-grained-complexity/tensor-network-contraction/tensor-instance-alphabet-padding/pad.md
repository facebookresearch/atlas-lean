# Alphabet padding of a tensor instance

Rename the active edge alphabet of an instance through `dec`, returning zero when any
off-diagonal target label is outside `D`. The diagonal coordinate is replaced by `sourceDefault`.
