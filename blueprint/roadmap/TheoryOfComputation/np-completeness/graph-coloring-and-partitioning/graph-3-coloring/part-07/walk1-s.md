# One step of the walk towards the farther endpoint

Given a stack $k$ of the 3-COLOR
verifier (used as a counter), a label $\ell$ and a pair of bits $(a, b)$ (the color of the
nearer endpoint), the statement pops the top symbol of $k$ and then moves the next color code
$(a', b')$ from the color stack $P$ onto the scratch stack $T$, rejecting if $P$ is empty. If $k$
was nonempty it continues at $\ell$. Otherwise $(a', b')$ is the color of the farther endpoint,
and the statement rejects if $(a', b') = (a, b)$ and continues at the restoring label
$\mathsf{back}$ if not.
