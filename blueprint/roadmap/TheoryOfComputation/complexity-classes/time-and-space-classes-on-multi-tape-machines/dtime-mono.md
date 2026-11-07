# Deterministic time classes are monotone up to affine changes of the bound

Let
$t_1, t_2 : \mathbb{N} \to \mathbb{N}$ and $a, b \in \mathbb{N}$ satisfy
$t_1(n) \le a \, t_2(n) + b$ for every $n \in \mathbb{N}$. Then
$\mathrm{DTIME}(t_1) \subseteq \mathrm{DTIME}(t_2)$.
