# Decidable languages have computable membership tests

Let $L$ be a language over an
alphabet $\sigma$ with a primitive recursive encoding. If membership in $L$ is decidable by a
multi-stack machine, then there is a computable function $f$ from words over $\sigma$ to
Booleans such that $L$ is the language of $f$, that is, the set of words $u$ with
$f(u) = \mathrm{true}$.
