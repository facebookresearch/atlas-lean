# Labels of the SAT tokenizer

The labels of the SAT tokenizer are: $\mathsf{un}(c)$ for a
bit $c$, which reads a unary count onto the clause counter $\mathsf{CC}$ if $c$ is true and onto
the literal counter $\mathsf{LC}$ otherwise; $\mathsf{cls}$, which starts a clause;
$\mathsf{lits}$, which starts a literal; $\mathsf{nm}(\ell)$, where $\ell$ is a bit or none,
which reads the bit pairs of a name block, $\ell$ being the last name bit read (none before the
first one); $\mathsf{pol}$, which reads the polarity and the next witness bit; $\mathsf{fin}$,
which checks that the formula stack $X$ is used up; and the halting labels $\mathsf{acc}$ and
$\mathsf{rej}$.
