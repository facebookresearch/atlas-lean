# The sequential transducer of a Mealy machine computes its transduction

For every Mealy
machine $M$, input word $x$ and output word $y$, the sequential transducer of $M$ translates $x$
to $y$ if and only if the transduction of $M$ on $x$ is $y$.

When the input and output alphabets lie in the same universe, the general translation relation of a Mealy machine, viewed as a transducer, is defined as the translation of its sequential transducer, so this also says: a Mealy machine relates $x$ to $y$ if and only if $y$ is its output word on $x$.
