# HAMPATH-verifier unary comparison with the counter restored

Let $\mathit{src}$,
$\mathit{sv}$, $c$ and the scratch stack $R$ be four distinct stacks of the HAMPATH verifier, and
let $\mathrm{cb}$, $\mathrm{rs}$ and $\mathrm{nx}$ be families of labels indexed by booleans such
that for every boolean $\mathit{ok}$ the instruction at $\mathrm{cb}(\mathit{ok})$ is the unary
comparison step on $\mathit{src}$, $\mathit{sv}$, $c$ with loop labels $\mathrm{cb}$, exit labels
$\mathrm{rs}$ and verdict $\mathit{ok}$, and the instruction at $\mathrm{rs}(\mathit{ok})$ is the
transfer loop that pops $R$ until it is empty, pushing one unit (the bit symbol of true) on $c$
per symbol popped, and then goes to $\mathrm{nx}(\mathit{ok})$. Write $1$ and $0$ for the bit
symbols of true and false, $1^k$ for $k$ copies of $1$, and $\bar r$ for the list of bit symbols
of a list of booleans $r$; stacks are listed from the top. Let $a, u \in \mathbb{N}$, let
$\mathit{ok}$ be a boolean, $r$ a list of booleans, $v$ a flag, and $\sigma$ stack contents with
$\sigma(\mathit{src}) = 1^a\,0\,\bar r$, $\sigma(c) = 1^u$ and $\sigma(R)$ empty. Then the verifier
runs in exactly $(a + 1) + (\min(a, u) + 1)$ steps from label $\mathrm{cb}(\mathit{ok})$ with flag
$v$ and stacks $\sigma$ to label $\mathrm{nx}(b)$, where $b$ is true exactly when $\mathit{ok}$ is
true and $a = u$, with some flag and with the stacks of $\sigma$ except that $\mathit{src}$ now
holds $\bar r$ and $\mathit{sv}$ holds $0\,1^a$ followed by $\sigma(\mathit{sv})$.
