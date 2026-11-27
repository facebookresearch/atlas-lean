# The 3-COLOR emitter machine

The program of the multi-stack Turing machine with the [stacks](k.md),
[stack alphabets](untitled.md) and [labels](lab.md) of the 3-COLOR emitter and a Boolean
internal state, which builds the 3-COLOR instance of a CNF formula from its token stack $T$. Below,
*moving the bit block* of a stack $A$ onto a stack $B$ means popping $A$ while its top is a name
bit and pushing each popped bit onto $B$; *moving the unit block* is the same with the clause-end
symbol $\mathrm{cl}$ in place of the name bits; *draining* a stack, pushing on given stacks, means
popping it until it is empty and pushing $\mathrm{cl}$ on each of those stacks once per popped
symbol (on $O$, the bit true). For a popped literal marker or name bit, "pushing it" pushes the
marker of the same polarity or the bit of the same value.

- $\mathsf{init}$: push the bits of the [palette triangle](pal.md) on $O$ (so that $O$ reads them
  top-first) and three $\mathrm{cl}$ on $N$, then go to $\mathsf{cls}$.
- $\mathsf{cls}$: if $T$ is empty, go to $\mathsf{pre}$ of the vertex-count site; otherwise pop
  $T$, and if the new top of $T$ is a literal marker push $\mathrm{cl}$ on $F$ and go to
  $\mathsf{lits}$, else go to $\mathsf{pre}(z_1)$.
- $\mathsf{lits}$: go to $\mathsf{pre}(o_1)$ if the top of $T$ is a literal marker and to
  $\mathsf{pre}(e_1)$ otherwise.
- $\mathsf{lp}$: pop the literal marker of $T$, push it on $P$ and go to $\mathsf{nm}$.
  $\mathsf{nm}$: move the bit block of $T$ onto $A$ and go to $\mathsf{walk}$.
- $\mathsf{walk}$: if $D$ is empty go to $\mathsf{back}$; otherwise pop the literal marker of $D$,
  push it on $E$ and go to $\mathsf{cmp}$.
- $\mathsf{cmp}$: compare the bit blocks of $A$ and $D$, popping both while their tops are equal
  bits and pushing each such bit on $X$ and on $B$; go to $\mathsf{rsA}(\mathrm{true})$ if both
  blocks end together and to $\mathsf{rsA}(\mathrm{false})$, without popping, at the first
  mismatch.
- $\mathsf{rsA}(e)$: move the bit block of $X$ onto $A$ and go to $\mathsf{rsD}(e)$.
  $\mathsf{rsD}(e)$: move the bit block of $B$ onto $D$, then go to $\mathsf{sel}$ if $e$ is true
  and to $\mathsf{mvN}$ with no bit otherwise.
- $\mathsf{sel}$: go to $\mathsf{mvN}(s)$, where $s$ is true exactly when the literal markers on
  top of $E$ and of $P$ have the same polarity.
- $\mathsf{mvN}(r)$: move the bit block of $D$ onto $E$, then go to $\mathsf{skU}$ if $r$ is no
  bit and to $\mathsf{mvU}(b)$ if $r$ is the bit $b$.
- $\mathsf{skU}$: move the unit block of $D$ onto $E$ and go to $\mathsf{walk}$.
  $\mathsf{mvU}(b)$: move the unit block of $D$ onto $U$, then go to $\mathsf{pre}(c_1)$ if $b$ is
  true and to $\mathsf{pre}(d_1)$ otherwise. $\mathsf{dr}$: drain $U$ pushing on $E$ and go to
  $\mathsf{walk}$.
- $\mathsf{back}$: if $E$ is empty go to $\mathsf{putN}$; otherwise pop the top of $E$ (a
  $\mathrm{cl}$, a literal marker or a name bit), push it on $D$ and go to $\mathsf{back}$.
- $\mathsf{putN}$: drain $N$ pushing on $D$ and $W$, then go to $\mathsf{putW}$. $\mathsf{putW}$:
  drain $W$ pushing on $N$, then go to $\mathsf{putA}$. $\mathsf{putA}$ and $\mathsf{putB}$: move
  the bit block of $A$ onto $B$, then that of $B$ onto $D$, then go to $\mathsf{putP}$.
  $\mathsf{putP}$: pop the literal marker of $P$, push it on $D$ and go to $\mathsf{aft}$.
- $\mathsf{aft}$: pop $F$; go to $\mathsf{fA}(\mathrm{true})$ if a symbol was popped and to
  $\mathsf{pre}(r_1)$ if $F$ was empty.
- $\mathsf{fA}(b)$: drain $N$ pushing on $R$ and $W$, then go to $\mathsf{fB}(b)$. $\mathsf{fB}(b)$:
  drain $W$ pushing on $N$, then go to $\mathsf{fC}(b)$. $\mathsf{fC}(b)$: push $0$ (if $b$ is
  true) or $4$ (if $b$ is false) symbols $\mathrm{cl}$ on $R$, then $2$ (if $b$ is true) or $5$
  (if $b$ is false) symbols $\mathrm{cl}$ on $N$, and go to $\mathsf{lits}$.
- $\mathsf{clr}(b)$: drain $R$ pushing on no stack, then go to $\mathsf{fA}(\mathrm{false})$ if $b$
  is true and to $\mathsf{cls}$ otherwise. $\mathsf{zN}$: push one $\mathrm{cl}$ on $N$ and go to
  $\mathsf{cls}$.
- For each [copy site](site.md) $j$: $\mathsf{pre}(j)$ pushes the [constant block](top.md) of $j$
  on $O$ so that $O$ reads it top-first, and goes to $\mathsf{cpA}(j)$; $\mathsf{cpA}(j)$ drains
  the stack of the [counter of $j$](src-2.md) pushing on $O$ and $W$, and goes to
  $\mathsf{cpB}(j)$; $\mathsf{cpB}(j)$ drains $W$ pushing on the stack of the counter of $j$, and
  goes to the [label that follows $j$](nxt.md).
- $\mathsf{done}$: halt.

In effect the machine pushes the palette triangle and sets $N = 3$; for each literal occurrence it
pushes the occurrence triangle, walks the earlier occurrences on $D$ pushing the consistency edges
with those of the same variable, and records the occurrence on $D$; after the first literal of a
clause it adds $N$ to the OR output $R$ and $2$ to $N$, and after a later literal it pushes an OR
gadget with inputs $N$ and $R$, sets $R$ to $N + 4$ and adds $5$ to $N$; a clause ends by joining
$R$ to the vertices $1$ and $2$ and clearing $R$, an empty clause joins $N$ to $0$, $1$ and $2$ and
adds $1$ to $N$, and at the end the vertex count $N$ is pushed.
