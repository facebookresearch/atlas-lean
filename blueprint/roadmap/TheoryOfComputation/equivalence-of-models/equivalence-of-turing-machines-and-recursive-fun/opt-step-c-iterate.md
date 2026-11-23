# The coded run simulates the machine's run

Let $o$ be either no configuration or a
configuration of a finite multi-stack machine all of whose stack symbols are relevant. Let
running one step send a running configuration to its successor, and a halted configuration or no
configuration to no configuration. Then for every $j$, applying the coded step on optional
configurations $j$ times to the coding of $o$ gives the coding of the result of running $j$
steps from $o$, and if running $j$ steps from $o$ gives a configuration, all of its stack symbols
are relevant.
