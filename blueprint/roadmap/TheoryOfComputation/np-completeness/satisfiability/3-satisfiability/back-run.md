# The 3SAT filter's return phase moves the side stack back

For either value of the cap
flag, all lists of symbols $M$ and $R$ such that every symbol of $M$ is a token symbol, and every
value $v$ of the Boolean variable, there is a value $v'$ such that the 3SAT clause-length filter
takes exactly $|M|$ steps from label $\mathsf{back}$ with variable $v$, token stack $R$ and side
stack $M$ to label $\mathsf{back}$ with variable $v'$, token stack the reversal of $M$ on top of
$R$, and empty side stack.
