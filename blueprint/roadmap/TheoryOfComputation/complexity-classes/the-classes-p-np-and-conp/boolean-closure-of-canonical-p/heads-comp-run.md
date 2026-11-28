# Running the head-combining component

For a fixed Boolean operation $\circ$ and bit lists $x$ and $w$ on its two stacks, the head-combining component runs in exactly two steps from label 0 with its internal state set to false to its true exit (label 3) if $h(w) \circ h(x)$ is true and to its false exit (label 4) otherwise, where $h$ of a list is its first bit, or false for the empty list. Both stacks are unchanged and the internal state ends equal to $h(x)$.
