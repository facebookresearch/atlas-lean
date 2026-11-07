# Non-universality makes the reduction language non-regular

Let $L$ be a language over an
alphabet $T$, let $T \sqcup \{\#, 0, 1\}$ extend $T$ by a separator $\#$ and two bits, and let
$R(L) = L\,\#\,\{0,1\}^* \cup T^*\,\#\,\{0^n1^n : n \in \mathbb{N}\}$ over this alphabet. If some
word $u$ over $T$ is not in $L$, then $R(L)$ is not regular.

The words $v$ over the bits with $u\,\#\,v \in R(L)$ are exactly the words $0^n1^n$.
