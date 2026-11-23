# Acting on a configuration

Let $k$ be a configuration with left cells $L$ (nearest
first), head cell $h$ and right cells $R$ (nearest first), let $q'$ be a state and let $s$ be an
action code. Acting on $k$ with $q'$ and $s$ gives a configuration with state $q'$, as follows.
For $s = 0$ (move left), its head cell is the first entry of $L$, or the blank $0$ if $L$ is
empty, its left cells are $L$ without its first entry, and its right cells are $h$ followed by
$R$. For $s = 1$ (move right), its head cell is the first entry of $R$, or $0$ if $R$ is empty,
its right cells are $R$ without its first entry, and its left cells are $h$ followed by $L$. For
$s = a + 2$ (write $a$), its head cell is $a$ and its left and right cells are $L$ and $R$.
