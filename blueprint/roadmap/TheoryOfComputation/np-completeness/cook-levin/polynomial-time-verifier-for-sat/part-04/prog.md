# The tokenizer program

The tokenizer is a multi-stack machine with stacks $X$ (formula
bits), $W$ (witness bits), $T$ (tokens), $B$ (table) and the unary counters $CC$, $LC$ (over the
unit symbol $\mathsf{cl}$), and one bit of internal state. Its instruction at each label is:

- $\mathsf{un}(\mathrm{true})$, $\mathsf{un}(\mathrm{false})$: read a unary count from $X$ onto
  $CC$ and $LC$ respectively. If the top of $X$ is the bit true, pop it, push $\mathsf{cl}$ onto
  the counter and stay; if it is the bit false, pop it and go to $\mathsf{cls}$ (from
  $\mathsf{un}(\mathrm{true})$) or $\mathsf{lits}$ (from $\mathsf{un}(\mathrm{false})$); otherwise
  go to $\mathsf{rej}$.
- $\mathsf{cls}$: pop $CC$; if it was non-empty go to $\mathsf{un}(\mathrm{false})$, else go to
  $\mathsf{fin}$.
- $\mathsf{lits}$: pop $LC$; if it was non-empty go to $\mathsf{nm}(\mathrm{none})$, else push
  $\mathsf{cl}$ onto $T$ and go to $\mathsf{cls}$.
- $\mathsf{nm}(\ell)$, where $\ell$ is an optional bit: if the top of $X$ is the bit true, pop it;
  then if the top of $X$ is a bit $s$, pop it, push the name bit $s$ onto $T$ and onto $B$ and go to
  $\mathsf{nm}(s)$, and otherwise go to $\mathsf{rej}$. If instead the top of $X$ is the bit false,
  pop it and go to $\mathsf{rej}$ if $\ell$ is the bit false and to $\mathsf{pol}$ otherwise. In
  any other case go to $\mathsf{rej}$.
- $\mathsf{pol}$: if the top of $X$ is a bit $p$, pop it and push $\mathsf{lit}(p)$ onto $T$; then
  if $W$ is non-empty, pop its top symbol, read as a bit $s$ (false if it is not a bit), and push
  $\mathsf{val}(s)$ onto $B$, and otherwise push $\mathsf{dead}$ onto $B$; go to $\mathsf{lits}$.
  If the top of $X$ is not a bit, go to $\mathsf{rej}$.
- $\mathsf{fin}$: go to $\mathsf{rej}$ if $X$ is non-empty and to $\mathsf{acc}$ if it is empty.
- $\mathsf{acc}$, $\mathsf{rej}$: halt.

Each test stores its outcome in the internal bit: whether the top of $X$ or $W$ has the stated
form, or, for the pop of $CC$ or $LC$, whether that counter was non-empty. Popping a name bit $s$
in $\mathsf{nm}(\ell)$, the polarity $p$ in $\mathsf{pol}$ or a witness symbol in $\mathsf{pol}$
stores the bit read ($s$, $p$ or the witness bit $s$); the remaining pops and all pushes leave the
internal bit unchanged. So after popping a bit of a unary count, or the closing bit false of a name
block, the internal bit is true.
