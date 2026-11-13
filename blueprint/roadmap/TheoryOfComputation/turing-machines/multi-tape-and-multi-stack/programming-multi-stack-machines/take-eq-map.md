# Recovering a bit block from its bits

Let $d$ be a decoder reading symbols as bits or
markers and $g$ an encoder from bits to symbols such that $g(b) = x$ whenever $d$ reads $x$ as the
bit $b$. If the symbol list $xs$ is a bit block for the bit list $u$ under $d$ and
$c = c_1 \cdots c_m$ is a prefix of $u$, then the first $m$ symbols of $xs$ are
$g(c_1), \dots, g(c_m)$.
