# The clause-family generator as a finite stack machine

For a layout $L$, tables
$\mathit{la}$, $\mathit{na}$, $\mathit{wa}$ and $N$ situations, the generator program for these
data, bundled as a multi-stack Turing machine with finitely many stacks, labels and states: its
stacks are the generator's stacks (the Boolean output stack and the counters), its input stack is
the time counter and its output stack is the Boolean output stack, its alphabets are the
generator's alphabets, its labels are the generator's labels for $N$ situations and literal
numbers below the number of literals of a clause, execution starts at the first precomputation
stage, and its internal state is a Boolean, initially false.
