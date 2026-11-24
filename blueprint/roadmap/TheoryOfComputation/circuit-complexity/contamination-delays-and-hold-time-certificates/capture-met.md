# Capture check at the receiving register

The register is clocked at time
`0`; its data input `s` holds its value at the edge from the setup time `setup`
plus the clock uncertainty `u` before the edge until the hold time `hold` plus
`u` after it, that is on `[-(setup + u), hold + u)`.
