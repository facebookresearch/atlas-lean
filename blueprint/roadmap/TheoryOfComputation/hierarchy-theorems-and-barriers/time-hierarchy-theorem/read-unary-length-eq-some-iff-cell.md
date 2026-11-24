# Reading a unary length prefix reads one cell

For bit lists $x$ and $r$ and a natural
number $n$, reading a unary length prefix of $x$ returns $n$ together with the rest $r$ if and
only if $x$ is the cell of $n$ (that is, $n$ copies of $\mathrm{true}$ followed by
$\mathrm{false}$) followed by $r$.
