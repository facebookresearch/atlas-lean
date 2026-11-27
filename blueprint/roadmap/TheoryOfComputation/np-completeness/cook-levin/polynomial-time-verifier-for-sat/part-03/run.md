# The clause check

Suppose the lookup sub-program $lk$ with entry label $l_0$ satisfies
the lookup contract with constants $a, b \in \mathbb{N}$. Let $\varphi$ be a CNF formula, $es$ a
list of table entries, $t$ the token list of $\varphi$ and $m$ the length of the table stack of
$es$. Start the driver with lookup $lk$ at its start label, with any internal state, with $t$
reversed on the token stack, the table stack of $es$ on the table stack, and the other six stacks
empty. Then within at most $|t| \cdot (a m + b + 5) + 1$ steps it reaches the label yes, with
some internal state and some stack contents, if every clause of $\varphi$ has a literal whose
polarity equals the value of its variable, and it reaches the label no otherwise. Here the value
of a variable $n$ is the value of the first entry of $es$ that is named by the binary encoding of
$n$ and has a value, or false if there is no such entry.
