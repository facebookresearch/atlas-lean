# Cleanup round

For a list $ks$ of stacks and labels $\mathit{self}$ and $\mathit{next}$,
the cleanup round is the statement that sets the state to the one storing the flag value false,
pops the stacks listed in $ks$ in order, once per entry (an empty stack stays empty), while
recording in the flag whether some pop found a symbol, and then goes to $\mathit{self}$ if one
did and to $\mathit{next}$ otherwise.
