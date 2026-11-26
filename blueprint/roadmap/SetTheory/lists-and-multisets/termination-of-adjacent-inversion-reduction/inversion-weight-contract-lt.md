# Contracting two entries decreases inversion weight

Replacing adjacent entries `i,j` by any entry `k` strictly decreases
inversion weight: `inversionWeight (p ++ k :: s) < inversionWeight (p ++ i :: j :: s)`.
No comparison among `i,j,k` is required.
