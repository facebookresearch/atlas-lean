# Walking along the marks of the PATH marking machine

Let $c$ be a stack other than the
marks stack $M$ and the parked stack $P$, let $u$ be a symbol of the alphabet of $c$, and let
$\ell$ be a label at which the program is the walk step counted by $c$ that returns to $\ell$
(with some final statement). Let $j$ be a natural number, $p$ and $q$ lists of bits, $v$ a
Boolean, and $S$ stack contents in which $c$ holds exactly $j$ copies of $u$, $M$ holds $q$ as
bit symbols, and $P$ holds the reverse of $p$ as bit symbols. Then there are a Boolean $v'$ and
stack contents $S'$ such that the machine goes in exactly $j$ steps from label $\ell$ with state
$v$ and stacks $S$ to label $\ell$ with state $v'$ and stacks $S'$, where $c$ is empty in $S'$,
$M$ holds $q$ with its first $j$ entries dropped, $P$ holds the reverse of the concatenation of
$p$ with the first $j$ entries of $q$, all as bit symbols, and $S'$ agrees with $S$ on every
stack other than $c$, $M$ and $P$.
