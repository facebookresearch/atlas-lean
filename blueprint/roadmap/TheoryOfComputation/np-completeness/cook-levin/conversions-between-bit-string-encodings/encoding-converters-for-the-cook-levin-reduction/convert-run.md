# Run of the pair-to-canonical converter

Let $x$ and $w$ be bit lists, write $x \# w$ for
the verifier input of the pair $(x, w)$, and read $1$ for true and $0$ for false. Let
$\mathrm{encFst}(x)$ replace each bit $b$ of $x$ by $1, 1, 1, b, 1, 0$ and $\mathrm{encSnd}(w)$
replace each bit $b$ of $w$ by $1, b, 0$. The program of the pair-to-canonical converter goes in
exactly $2|x| + 2|w| + 5$ steps from the configuration at label $\mathrm{readFst}$ with empty
state, $x \# w$ on the input stack and the output stack and both stashes empty, to the halted
configuration with empty state, empty input stack and stashes, and output stack reading
$\mathrm{encFst}(x)$, then $0$, then $\mathrm{encSnd}(w)$ from the top.
