# Relabelling in the verifier host

Given labels $\mathit{yes}$ and $\mathit{no}$ of a
component machine $c$, a label $l$ of $c$ is sent to the host label that starts the cleanup with
answer true if $l = \mathit{yes}$, to the host label that starts the cleanup with answer false if
$l \ne \mathit{yes}$ and $l = \mathit{no}$, and to the host label that runs the component at $l$
otherwise.
