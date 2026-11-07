# Occurrence table of a nonempty list

Let $n$ be a natural number, $L$ a list of natural
numbers and $w$ a list of bits. The occurrence table of the list $n$ followed by $L$, with $w$, is
the entry whose name is the binary code of $n$ and whose value is the first bit of $w$ (no value
if $w$ is empty), followed by the occurrence table of $L$ with $w$ minus its first bit (with the
empty list if $w$ is empty).
