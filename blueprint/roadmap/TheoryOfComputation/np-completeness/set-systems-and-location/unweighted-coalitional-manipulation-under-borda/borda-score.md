# Borda scores

The Borda score of candidate $d$ under a list $V$ of votes over $m$ candidates is the sum, over the votes, of the points $d$ receives from the Borda scoring vector $(m - 1, m - 2, \dots, 0)$; a candidate missing from a vote $v$ receives the entry of the scoring vector at position $|v| + 1$ ($m - 1 - |v|$ points when $|v| < m$, otherwise $0$), and a candidate ranked beyond the scoring vector receives $0$.
