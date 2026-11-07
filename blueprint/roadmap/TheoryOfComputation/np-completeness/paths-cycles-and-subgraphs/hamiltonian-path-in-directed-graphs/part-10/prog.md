# The Hamiltonian path verifier machine

The verifier is the program of the multi-stack
machine with the stacks and labels of the Hamiltonian path verifier, every stack over the
alphabet $\mathrm{Sym}$, and a Boolean internal variable, given below label by label. Write
$\mathrm{bit}(x)$ for the bit symbol of a boolean $x$. Write $(a, n)$, $(a, s)$, $(c, n)$ and
$(b, t)$ for the four counter comparisons, and $\alpha(i)$ and $\beta(i)$ for the first and the
second counter of comparison $i$. Every unary reader, unary mover, bit-moving loop and transfer
below has the label it sits at as its own label; the bit-moving loops read bit symbols as bits
and every other symbol as a marker, and push $\mathrm{bit}(x)$ for a bit $x$. The transfer from a
stack $k$ onto a list of stacks with next label $m$ pops $k$; if it popped a symbol, it pushes
$\mathrm{bit}(\mathrm{true})$ onto each listed stack and returns to its own label, and otherwise
it goes to $m$. An emptiness test of a stack "to $e$, else $e'$" goes to $e$ if the stack is
empty and to $e'$ otherwise. A transfer also stores in the Boolean variable whether its pop
found a symbol, and an emptiness test stores there whether the stack is empty.

- $\mathsf{rdS}$, $\mathsf{rdT}$, $\mathsf{rdN}$: the unary reader from $X$ onto $S$, $T$, $N$
  respectively, with next labels $\mathsf{rdT}$, $\mathsf{rdN}$, $\mathsf{vE}$ respectively.
- $\mathsf{vE}$: the emptiness test of $X$ to $\mathsf{vEb}$, else $\mathsf{vEU}$. $\mathsf{vEU}$
  and $\mathsf{vEV}$: the unary mover from $X$ to $E$, with next labels $\mathsf{vEV}$ and
  $\mathsf{vE}$ respectively. $\mathsf{vEb}$: the bit-moving loop from $E$ to $X$ with next label
  $\mathsf{vW}$.
- $\mathsf{vW}$: the emptiness test of $W$ to $\mathsf{vWb}$, else $\mathsf{vWU}$. $\mathsf{vWU}$:
  the unary mover from $W$ to $Z$ with next label $\mathsf{vW}$. $\mathsf{vWb}$: the bit-moving
  loop from $Z$ to $W$ with next label $\mathsf{loop}$.
- $\mathsf{loop}$: the emptiness test of $W$ to $\mathsf{cmp}(c, n)$, else $\mathsf{rdA}$.
  $\mathsf{rdA}$: the unary reader from $W$ onto $A$ with next label $\mathsf{cmp}(a, n)$.
  $\mathsf{hd}$: the emptiness test of $C$ to $\mathsf{cmp}(a, s)$, else $\mathsf{scan}$.
- For each comparison $i$, $\mathsf{cmp}(i)$ is one round of counter comparison of $\alpha(i)$
  and $\beta(i)$, with scratch stacks $R$ (for $\alpha(i)$) and $Q$ (for $\beta(i)$), both units
  $\mathrm{bit}(\mathrm{true})$, own label $\mathsf{cmp}(i)$, and $\mathsf{cr}(i, <)$,
  $\mathsf{cr}(i, =)$, $\mathsf{cr}(i, >)$ as its labels $\mathit{lt}$, $\mathit{eq}$ and
  $\mathit{gt}$. For each ordering $o$, $\mathsf{cr}(i, o)$ is the transfer from $R$ onto
  $\alpha(i)$ with next label $\mathsf{crb}(i, o)$, and $\mathsf{crb}(i, o)$ is the transfer from
  $Q$ onto $\beta(i)$ whose next label is the exit label of the counter comparison $i$ with
  outcome $o$.
- $\mathsf{scan}$: the emptiness test of $X$ to $\mathsf{no}$, else
  $\mathsf{ceU}(\mathrm{true})$. For each boolean $\mathit{ok}$: $\mathsf{ceU}(\mathit{ok})$ is
  the step of the unary comparison loop with source $X$, save stack $E$, counter $B$, label
  families $\mathsf{ceU}$ and $\mathsf{rsU}$, and verdict $\mathit{ok}$; $\mathsf{rsU}(\mathit{ok})$
  is the transfer from $R$ onto $B$ with next label $\mathsf{ceV}(\mathit{ok})$;
  $\mathsf{ceV}(\mathit{ok})$ is the step of the unary comparison loop with source $X$, save stack
  $E$, counter $A$, label families $\mathsf{ceV}$ and $\mathsf{rsV}$, and verdict $\mathit{ok}$;
  and $\mathsf{rsV}(\mathit{ok})$ is the transfer from $R$ onto $A$ with next label $\mathsf{scB}$
  if $\mathit{ok}$ is true and $\mathsf{scan}$ otherwise. $\mathsf{scB}$: the bit-moving loop from
  $E$ to $X$ with next label $\mathsf{nd}$.
- $\mathsf{nd}$: the emptiness test of $W$ to $\mathsf{ndB}$, else $\mathsf{cbN}(\mathrm{true})$.
  For each boolean $\mathit{ok}$: $\mathsf{cbN}(\mathit{ok})$ is the step of the unary comparison
  loop with source $W$, save stack $Z$, counter $A$, label families $\mathsf{cbN}$ and
  $\mathsf{rsN}$, and verdict $\mathit{ok}$; and $\mathsf{rsN}(\mathit{ok})$ is the transfer from
  $R$ onto $A$ with next label $\mathsf{no}$ if $\mathit{ok}$ is true and $\mathsf{nd}$
  otherwise. $\mathsf{ndB}$: the bit-moving loop from $Z$ to $W$ with next label $\mathsf{incC}$.
- $\mathsf{fin}$: the emptiness test of $C$ to $\mathsf{no}$, else $\mathsf{cmp}(b, t)$.
  $\mathsf{incC}$: the counter increment pushing $\mathrm{bit}(\mathrm{true})$ onto $C$ and going
  to $\mathsf{dB}$. $\mathsf{dB}$: the transfer from $B$ onto no stack (it drains $B$) with next
  label $\mathsf{mA}$. $\mathsf{mA}$: the transfer from $A$ onto $B$ with next label
  $\mathsf{loop}$.
- $\mathsf{yes}$ and $\mathsf{no}$: halt.

The verifier parses and validates the input and the witness, then walks the vertices.
