# Completions of specified transitions

A total transition function $d$ on states $\{0, \dots, n - 1\}$ and letters $\{0, \dots, m - 1\}$ extends the specified transitions when $d(q, a) = q'$ for every listed entry $((q, a), q')$ with $q < n$ and $a < m$; the target $q'$ must then equal $d(q, a)$, hence be below $n$. Listed entries whose state or letter is out of range impose no condition: with one state, a listed transition from state $1$ constrains nothing. Well-formed instances list only in-range entries, and for them $d$ is a completion of the specified transitions in the usual sense.
