# Serial histories of read-write transactions

Consider $n$ transactions $t < n$, each consisting of a read $R_t$ followed by a write $W_t$, and a
history $h$, a list of such operations. The history is serial when for every $t < n$, the first
occurrence of $W_t$ in $h$ comes immediately after the first occurrence of $R_t$: their positions
satisfy $\operatorname{pos}(W_t) = \operatorname{pos}(R_t) + 1$, where the position of an operation
that does not occur is the length of $h$. This is the notion of the serializability problem for
database histories, not the [serial schedules](../../../../ComputerScience/databases/conflict-serializability/is-serial.md)
of conflict serializability, where all operations of each transaction are contiguous.
