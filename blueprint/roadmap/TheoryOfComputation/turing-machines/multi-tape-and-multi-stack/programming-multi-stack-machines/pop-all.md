# Popping a list of stacks

For a list $ks$ of stacks and a statement $q$, this is the
statement that pops the stacks listed in $ks$ in order, once per entry (an empty stack stays
empty), after each pop replacing the state by the one storing the old flag or-ed with whether
that pop found a symbol, and then continues with $q$.
