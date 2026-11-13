# Relabelling preserves computing a function within time and space bounds

Let $M$ and $M'$
be deterministic machines with $k$ work tapes over the same alphabet such that $M'$ simulates $M$
up to a state relabelling $f$. Let $e_{\mathrm{in}}$ and $e_{\mathrm{out}}$ be injective encodings
of types $\alpha$ and $\beta$ as words over the alphabet, $g : \alpha \to \beta$ a function and
$t, s : \alpha \to \mathbb{N}$ bounds. Then $M'$ computes $g$ with respect to these encodings in
time $t$ and space $s$ if and only if $M$ does. Here a machine does so when, for every
$a \in \alpha$, on input $e_{\mathrm{in}}(a)$ it eventually halts with output
$e_{\mathrm{out}}(g(a))$, every computation path of at least $t(a)$ steps ends halted, and every
computation path visits at most $s(a)$ work-tape cells.
