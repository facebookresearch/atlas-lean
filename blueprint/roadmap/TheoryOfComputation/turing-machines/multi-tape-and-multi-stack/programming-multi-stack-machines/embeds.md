# Embedding of a machine in a host

Let $E$ be a stack embedding and $\varphi$ a map from
the labels of a machine $M$ to the labels of a host machine $M'$ over the same internal states.
Then $M$ embeds in $M'$ along $E$ and $\varphi$ when, for every label $\ell$ of $M$, either the
statement of $M'$ at $\varphi(\ell)$ is the statement of $M$ at $\ell$ translated along $E$ and
$\varphi$, or the statement of $M$ at $\ell$ is the halt statement (in which case $M'$ may do
anything at $\varphi(\ell)$).
