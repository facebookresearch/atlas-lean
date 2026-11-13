# Step of the HAMPATH verifier's unary comparison loop

For stacks $\mathit{src}$,
$\mathit{sv}$, $c$ of the HAMPATH verifier, label families $\mathit{self}$ and $\mathit{fin}$
indexed by booleans, and a boolean verdict $\mathit{ok}$, this is the instruction that pops the top
of $\mathit{src}$, reads it as a bit $b$ (false if $\mathit{src}$ is empty or its top is not a bit
symbol), and pushes the bit symbol of $b$ onto $\mathit{sv}$. If $b$ is true, it pops $c$; if $c$
was nonempty it pushes the bit symbol of true onto the scratch stack $R$ and goes to
$\mathit{self}(\mathit{ok})$, and otherwise it goes to $\mathit{self}(\mathrm{false})$. If $b$ is
false, it goes to $\mathit{fin}(\mathit{ok})$ when $c$ is empty and to
$\mathit{fin}(\mathrm{false})$ otherwise.

Iterated, it compares the next unary number of $\mathit{src}$ with the counter $c$, one unit of $c$
per true, parked on $R$: $\mathit{ok}$ is the verdict so far, falsified when $c$ runs out early.
