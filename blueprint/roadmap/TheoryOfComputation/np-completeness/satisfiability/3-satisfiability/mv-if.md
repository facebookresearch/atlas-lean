# Conditional move between stacks

For stacks $a$ and $b$ of the filter, a symbol $s$, a
label $\ell$ and a statement $q$: the statement that tests whether the top of stack $a$ is $s$ and
sets the internal state to the outcome; if it is, it pops $a$, pushes $s$ onto $b$ and jumps to
$\ell$, and otherwise it runs $q$.
