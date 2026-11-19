# Counters after a multi-target transfer

Given counter values $F : C \to \mathbb{N}$, a
counter $x \in C$ and a list $Y$ of counters, the counter values after transferring $x$ to $Y$
form the function that sends $x$ to $0$, sends every $z \ne x$ occurring in $Y$ to
$F(z) + F(x)$, and sends every other $z$ to $F(z)$.
