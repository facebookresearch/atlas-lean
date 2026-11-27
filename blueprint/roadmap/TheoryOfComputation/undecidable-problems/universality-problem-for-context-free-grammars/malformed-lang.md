# Malformed words

Consider words over $\alpha \oplus \mathrm{Bool}$, whose symbols are
letters from $\alpha$ and bits, and read the bit $\mathrm{true}$ as the separator $|$ and the bit
$\mathrm{false}$ as $1$. For $k \in \mathbb{N}$, a word is malformed with bound $k$ when at least
one of the following holds: it consists of letters only (possibly none); it is a word of letters
followed by a nonempty word of bits whose first bit is $1$; some bit is immediately followed by a
letter; or it contains the block $|\,1^k$ (the bit $|$ followed by $k$ bits $1$) as a contiguous
factor.
