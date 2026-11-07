# Pair encoding $w \# y$

For bit strings $w$ and $y$, the word over the pair alphabet
$G = \mathrm{Bool} \oplus \mathrm{Option}\,\mathrm{Bool}$ consisting of the bits $b$ of $w$ in
order, each tagged on the left as $\mathrm{inl}\,b$, then the separator
$\# = \mathrm{inr}\,\mathrm{none}$, then the bits $b$ of $y$ in order, each tagged on the right as
$\mathrm{inr}(\mathrm{some}\,b)$. This is the input of the dense CNF-SAT verifier.
