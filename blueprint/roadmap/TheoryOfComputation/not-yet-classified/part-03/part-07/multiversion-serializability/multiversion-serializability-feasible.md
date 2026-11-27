# Multiversion serializability

An instance consists of a number $n$ of transactions and a schedule $S$ of read and write actions on variables. An interpretation of $S$ assigns each read either the position of an earlier write of the same variable or the original value. The instance is feasible when some interpretation of $S$ leaves every variable with the same final value as the standard interpretation (each read sees the latest earlier write) of the serial schedule that runs the transactions $0, \dots, n - 1$ in some order, each with its actions in their order in $S$.
