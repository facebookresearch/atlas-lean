# Run of the literal routine of the accept generator

Let $c$ be a clause kind with base
counter $b(c)$, offset $\mathrm{off}(c)$ and polarity $\sigma(c)$, and let $F$ assign values to
the counters of the accept generator (for layout $L$ and parameters $n_1$, $\mathrm{ac}$, $k_1$,
$\mathrm{ea}$) such that the scratch counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$
are $0$. Let $q, m \in \mathbb{N}$ with $q = F(b(c)) + \mathrm{off}(c)$ and
$F(P) = q + m + 1$. Then for every output word $o$ and every Boolean state $v$, the generator
runs in at most $m(3q + 6) + 2F(b(c)) + 4q + 9$ steps from the label
$\mathrm{lit}(c, \mathrm{cp1})$, with state $v$, counters $F$ and output $o$, to the label
$\mathrm{fin}(c)$, with state false, the counters $F$ except that $P$ holds $q$, and output
$s\,z\,o$. Here $s$ is the two bits true, $\lnot\sigma(c)$ (the encoding of a slot holding a
literal of polarity $\sigma(c)$), and $z$ is $m$ copies of the two bits false, true (the
encoding of $m$ empty slots).
