# The composite machine

Let $M_1$ and $M_2$ be finite multi-stack Turing machines, let $X$ be
the alphabet of the input stack of $M_2$, and let $\varphi$ map the output alphabet of $M_1$ to $X$.
The composite machine has the stacks of $M_1$, the stacks of $M_2$ and one scratch stack with
alphabet $X$; its input stack is that of $M_1$ and its output stack is that of $M_2$. It starts
at the main label of $M_1$, in the state made of the initial states of $M_1$ and $M_2$ and no held
symbol. It runs $M_1$; when $M_1$ halts, it pops the output stack of $M_1$ onto the scratch stack,
translating each symbol by $\varphi$, then pops the scratch stack onto the input stack of $M_2$,
then runs $M_2$ from its main label, and it halts when $M_2$ halts.
