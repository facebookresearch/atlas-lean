# The I3 loop

Let $L$ be a layout with $g$ symbol codes, consider the init generator for a
start code, a stack $k_0$ and a list of $\ell$ certificate codes, and let
$x = (x_0, \dots, x_{s-1})$ be a list of codes $x_j < g$. Suppose its counters $F$ have $Q$,
$\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$, $\mathrm{CB}$ and $P$ equal to $0$,
$\mathrm{Vc} = V$, $\mathrm{Gc} = g$ and $\mathrm{ZA} = Z$, that $jg + Z + g \le V$ for every
$j < s$, and that $s \le N_b$. Then for every $r \le s$, every output $o$ and every flag $v$, the
generator, started at the head of the I3 loop with flag $v$, the counters of $F$ except
$\mathrm{Xn} = r$, output $o$, and $x_{r-1}, \dots, x_1, x_0$ on its input stack (top first),
reaches in at most $r\beta + 1$ steps the head of the I2 loop over the stacks above $k_0$, with
flag false, the counters of $F$ except $\mathrm{Xn} = 0$, an empty input stack, and output
$e_0 e_1 \cdots e_{r-1}$ followed by $o$. Here $e_j$ is the encoding of the dense clause over
$V$ variables whose only literal is the positive literal of variable $jg + Z + x_j$, and
$\beta = 3V^2 + 12V + (\ell + 2)(6V + 9) + (2g + 4)N_b + g + 10$.
