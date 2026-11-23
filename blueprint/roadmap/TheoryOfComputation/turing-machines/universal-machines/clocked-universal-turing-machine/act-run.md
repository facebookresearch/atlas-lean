# The tape update

Let $c$ be a code, $k$ a configuration and $t$, $q'$, $s$ natural
numbers. Started at the label $\mathsf{act0}$, with any value of its internal variable, on the
stacks holding the code $c$, the clock $t$ and the configuration $k$, with $q'$ on the next-state
stack, $s$ on the action stack and all other stacks empty, the program of the clocked universal
machine reaches the label $\mathsf{fin}$, with some value of its internal variable, on the stacks
holding $c$, $t$ and the configuration obtained from $k$ by entering the state $q'$ and doing the
action coded by $s$, with the next-state, action and all other stacks empty. It does so in at
most as many steps as the step bound of the tape update for $k$, $q'$ and $s$.
