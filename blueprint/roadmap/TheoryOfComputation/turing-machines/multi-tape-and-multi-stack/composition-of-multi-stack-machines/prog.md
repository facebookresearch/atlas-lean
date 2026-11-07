# The program of the composite machine

Let $M_1$ and $M_2$ be finite multi-stack Turing
machines and $\varphi$ a map from $M_1$'s output alphabet to $M_2$'s input alphabet. At a label
of $M_1$ or of $M_2$ the composite program runs the lifted statement of that machine at that
label. At the pop label of the first copy loop it pops $M_1$'s output stack, stores the image
under $\varphi$ of the popped symbol (or nothing) in the third state component, and jumps to the
push label of the first loop for that image, or to the pop label of the second loop if the
stack was empty. At the push label of the first loop for $x$ it pushes $x$ on the scratch stack
and jumps to the first pop label. At the pop label of the second loop it pops the scratch
stack, stores the popped symbol (or nothing) in the third state component, and jumps to the
push label of the second loop for that symbol, or to the copy of $M_2$'s main label if the
scratch stack was empty. At the push label of the second loop for $x$ it pushes $x$ on $M_2$'s
input stack and jumps to the second pop label.
