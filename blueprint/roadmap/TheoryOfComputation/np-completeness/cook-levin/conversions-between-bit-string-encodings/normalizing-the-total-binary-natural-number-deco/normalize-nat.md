# Normalization of a raw binary natural-number payload

The *binary code* of a natural number $n$ is its binary digits, least significant first, with no trailing zero
(empty for $n = 0$); write $1$ for true and $0$ for false.

For a bit string $x$, its normalization is $x1$ (the string $x$ followed by a $1$) if the last bit of $x$ is
$0$, and $x$ itself otherwise (in particular when $x$ is empty or ends with $1$).

The result is computed directly from $x$, without computing the number $x$ denotes.
