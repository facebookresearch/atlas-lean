# Translating a statement along a stack embedding

Let $E$ be a stack embedding with stack
renaming $e$ and alphabet bijections $\iota_k$, and let $\varphi$ map the sub-machine's labels to
the host's labels. The translation of a sub-machine statement is the host statement obtained
recursively, where $s$ denotes the current state. A push of the symbol $f(s)$ on stack $k$
becomes a push of $\iota_k(f(s))$ on stack $e(k)$. A peek or pop on stack $k$ becomes a peek or
pop on stack $e(k)$ whose result is mapped back by $\iota_k^{-1}$ before the state update. A jump
to label $f(s)$ becomes a jump to $\varphi(f(s))$. State updates, branches and halt are kept, with
their sub-statements translated.
