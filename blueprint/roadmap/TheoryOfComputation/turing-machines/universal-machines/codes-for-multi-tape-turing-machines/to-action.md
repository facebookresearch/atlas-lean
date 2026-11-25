# Decoding a coded action

A coded action $a$ stands for the action of a deterministic multi-tape
Turing machine with $k$ work tapes, the binary alphabet and states in $\mathbb{N}$ that moves the input head by the decoded input move of $a$, on each work tape writes the
optional symbol that $a$ gives for that tape and moves its head by the decoded move, emits the
optional output bit of $a$, and enters the next state of $a$ (halting when there is none).
