# Weft of an encoded gate

Given a list $w$ of wefts of earlier gates, where $w_a$ reads as
$0$ when $a$ is not a position of $w$, the weft of an encoded gate $(k, r)$ is $1$ if it is a
large AND or OR gate ($k \in \{3, 4\}$ and $r$ has more than $2$ entries) and $0$ otherwise,
plus the maximum of $w_a$ over the entries $a$ of its predecessor list (the maximum over an
empty list is $0$). In particular, input and constant gates have weft $0$.
