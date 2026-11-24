# Decoding a prefix-coded natural number

Given a bit string $w$, writing $1$ for true and
$0$ for false, the decoder reads one self-delimiting block $1\,b_1\,1\,b_2 \cdots 1\,b_k\,0$ from
the front of $w$, with payload $b_1 \cdots b_k$ and remaining bits $r$. If the payload is the
binary expansion of some natural number $n$, least significant bit first and without trailing
zeros (empty for $n = 0$), the result is $(n, r)$. Decoding fails if $w$ does not begin with such
a block or the payload is not of this form.
