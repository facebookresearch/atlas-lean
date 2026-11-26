# Size subst le tight

Size of a substitution, tight form: if every substituted formula has at most `D` gates, then
`(g.subst wiring).size ≤ g.size * (D + 1) + D = g.size + (g.size + 1) * D`. The gates of `g`
remain, and `g` has at most `g.size + 1` leaves, each replaced by at most `D` gates.
