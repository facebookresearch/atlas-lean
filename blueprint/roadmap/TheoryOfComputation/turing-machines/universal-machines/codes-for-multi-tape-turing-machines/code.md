# Codes for multi-tape machines

A code for a machine with $k$ work tapes over the binary
alphabet, with states in $\mathbb{N}$, is a finite list of table entries, each a key (a state
together with the symbols under the input head and the $k$ work heads) paired with a coded
action. The table is looked up by key, the first matching entry wins, and a missing key halts
the machine.
