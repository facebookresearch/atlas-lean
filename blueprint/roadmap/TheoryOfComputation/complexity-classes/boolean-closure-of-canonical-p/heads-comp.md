# The head-combining component

For a fixed Boolean operation $\circ$, a two-stack program component with five labels: it peeks at the head of the second stack, then at the head of the first, and jumps to label 3 (true exit) or label 4 (false exit) according to whether (second head) $\circ$ (first head) is true. An empty stack counts as having head false.
