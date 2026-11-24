# Moving a marker onto the scan buffer

For a label $\ell$, this instruction pops the top
symbol of the code stack $C$ and discards it (doing nothing if $C$ is empty), pushes a marker (the
bit false) onto the scan buffer $B$, and goes to $\ell$; the state bit is unchanged.
