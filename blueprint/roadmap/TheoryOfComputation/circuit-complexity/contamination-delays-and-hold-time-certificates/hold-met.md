# Hold check at the receiving register

The register is clocked at time
`0`; its data input `s` must not change from the edge until the hold time `hold`
plus the clock uncertainty `u`, that is on `[0, hold + u)`.
