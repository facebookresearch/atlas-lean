# Run of the accept generator's precomputation

Fix a layout $L$ with label/state block
size $A$, $K$ stacks and $g$ symbol codes, and naturals $n_1$, $a$, $k_1$, $e$. For all
$T, H \in \mathbb{N}$ and every list $o$ of Booleans, write $W = A + K H g$ for the row width.
The accept generator, started at its first precomputation label with internal state false,
output $o$, $T$ units on counter $\mathsf{Tn}$, $H$ units on $\mathsf{Hs}$ and every other
counter empty, reaches in at most $\mathrm{preB}(L, k_1, T, H)$ steps the first clause label
with internal state false, output still $o$, and counters $\mathsf{Tn} = T + 1$,
$\mathsf{Hs} = H$, $\mathsf{Gc} = g$, $\mathsf{HG} = H g$, $\mathsf{Wc} = W$, $\mathsf{Kc} = K$,
$\mathsf{K1} = k_1$, $\mathsf{Vc} = (T + 1) W$, $\mathsf{TW} = T W$,
$\mathsf{CB} = T W + A + k_1 H g$, and every other counter empty.
