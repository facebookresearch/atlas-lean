# Output block of an edge number

For $q \in \mathbb{N}$ and a bit $b$: if $b$ is true, the
block is $q$ copies of $(\mathrm{true}, \mathrm{false}, \mathrm{true}, \mathrm{false})$ followed by
$(\mathrm{true}, \mathrm{true}, \mathrm{false})$; if $b$ is false, it is the one-bit list
$(\mathrm{false})$.

This is the self-delimiting binary code of $4^q$ when $b$ is true and of $0$ when $b$ is false.
