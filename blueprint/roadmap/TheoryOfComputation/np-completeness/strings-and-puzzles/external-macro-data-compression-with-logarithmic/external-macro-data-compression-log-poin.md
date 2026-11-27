# Instances of EXTERNAL MACRO DATA COMPRESSION with a fixed alphabet and logarithmic pointer cost

An instance is a raw triple $(s, h, B)$: a word $s$ given as a list of natural numbers, and natural numbers $h$ and $B$. The type has no alphabet parameter: the word `[1]` decodes even when the alphabet is $\{0\}$ ($k = 1$); [validation](well-formed.md), not the tuple type, checks the letters of $s$.
