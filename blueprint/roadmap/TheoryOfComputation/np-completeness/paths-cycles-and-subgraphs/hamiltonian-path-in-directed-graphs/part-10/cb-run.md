# Run of the HAMPATH verifier's unary comparison loop

Let $\mathit{src}$, $\mathit{sv}$, $c$
and the scratch stack $R$ be four distinct stacks of the HAMPATH verifier, and let $\mathrm{cb}$ and
$\mathrm{fin}$ be families of labels indexed by booleans such that for every boolean $\mathit{ok}$
the instruction at $\mathrm{cb}(\mathit{ok})$ is the unary comparison step on $\mathit{src}$,
$\mathit{sv}$, $c$ with loop labels $\mathrm{cb}$, exit labels $\mathrm{fin}$ and verdict
$\mathit{ok}$. Write $1$ and $0$ for the bit symbols of true and false, $1^k$ for $k$ copies of
$1$, and $\bar r$ for the list of bit symbols of a list of booleans $r$; stacks are listed from the
top. Then for all $a, u, j \in \mathbb{N}$, every boolean $\mathit{ok}$, every list of booleans
$r$, every flag $v$ and all stack contents $\sigma$ with $\sigma(\mathit{src}) = 1^a\,0\,\bar r$,
$\sigma(c) = 1^u$ and $\sigma(R) = 1^j$, the verifier runs in exactly $a + 1$ steps from label
$\mathrm{cb}(\mathit{ok})$ with flag $v$ and stacks $\sigma$ to label $\mathrm{fin}(b)$, where $b$
is true exactly when $\mathit{ok}$ is true and $a = u$, with some flag and some stacks $\sigma'$
such that $\sigma'(\mathit{src}) = \bar r$, $\sigma'(\mathit{sv}) = 0\,1^a\,\sigma(\mathit{sv})$,
$\sigma'(c) = 1^{\max(u - a, 0)}$, $\sigma'(R) = 1^{\min(a, u) + j}$, and $\sigma'(k) = \sigma(k)$
for every other stack $k$.
