# The SAT-to-3SAT emitter machine

The emitter is the multi-stack machine on the stacks
$T, O, U, Z, W, C$ of the emitter ($O$ holds bits, the others token symbols), with the labels of
the emitter and one internal Boolean variable. A unit is the clause symbol, and prepending bits
$b_1, \dots, b_k$ to $O$ pushes them so that $O$ reads $b_1, \dots, b_k$ from the top. The labels
act as follows.

* $\mathrm{start}$: if $T$ is empty, push $\text{false}$ on $O$ and go to $\mathrm{fin}$;
  otherwise pop $T$ and go to $\mathrm{clause}$.
* $\mathrm{clause}$: if the top of $T$ is a literal marker, go to $\mathrm{lit}(\text{true})$;
  otherwise push a unit on $C$, push $\text{false}$ on $O$ and go to $\mathrm{start}$.
* $\mathrm{lit}(f)$: pop $T$, set the variable $p$ to whether the popped symbol is the literal
  marker of polarity true, and go to $\mathrm{body}(\text{true}, p)$ if $f$ holds and to
  $\mathrm{fa}(\text{true}, p)$ otherwise.
* $\mathrm{fa}(s, x)$: prepend $\text{true}, \text{true}, \text{false}, s$ to $O$ and go to
  $\mathrm{fb}(s, x)$.
* $\mathrm{fb}(s, x)$: pop $U$ until it is empty, pushing a unit on $Z$ and on $W$ per popped
  symbol, then go to $\mathrm{fc}(s, x)$.
* $\mathrm{fc}(s, x)$: pop $W$ until it is empty, pushing a unit on $U$ per popped symbol, then
  go to $\mathrm{fd}(s, x)$.
* $\mathrm{fd}(s, x)$: pop $Z$ until it is empty, prepending $\text{true}, \text{false}$ to $O$
  per popped symbol, then go to $\mathrm{fe}(s, x)$.
* $\mathrm{fe}(\text{true}, p)$: push a unit on $U$, prepend $\text{true}, \text{true}$ to $O$
  and go to $\mathrm{body}(\text{false}, p)$. $\mathrm{fe}(\text{false}, f)$: prepend
  $\text{true}, \text{true}$ to $O$ and go to $\mathrm{sfx}(f)$.
* $\mathrm{body}(f, p)$: prepend $\text{false}, p$ to $O$ and go to $\mathrm{cp}(f, \text{false})$.
* $\mathrm{cp}(f, e)$: if the top of $T$ is a bit symbol $b$, pop it, prepend $\text{true}, b$ to
  $O$ and go to $\mathrm{cp}(f, \text{true})$; otherwise prepend $\text{true}, \text{false}$ to
  $O$ if $e$ holds, and go to $\mathrm{aft}(f)$.
* $\mathrm{aft}(f)$: if the top of $T$ is a literal marker, go to $\mathrm{fa}(\text{false}, f)$;
  otherwise push a unit on $C$, prepend $k$ copies of $\text{true}$ and then $\text{false}$ to
  $O$, where $k = 1$ if $f$ holds and $k = 2$ otherwise, and go to $\mathrm{start}$.
* $\mathrm{sfx}(f)$: push a unit on $C$, prepend $k$ copies of $\text{true}$ and then
  $\text{false}$ to $O$, where $k = 2$ if $f$ holds and $k = 3$ otherwise, and go to
  $\mathrm{lit}(\text{false})$.
* $\mathrm{fin}$: pop $C$ until it is empty, prepending $\text{true}$ to $O$ per popped symbol,
  then go to $\mathrm{done}$.
* $\mathrm{done}$: halt.

Each test of a stack top and each pop of a loop also stores its outcome in the internal
variable.
