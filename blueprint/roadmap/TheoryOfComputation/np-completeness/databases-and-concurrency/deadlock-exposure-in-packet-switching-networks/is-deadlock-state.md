# Deadlock states

A list $P$ of packets is a deadlock state when every packet names a route and a position on it; no vertex holds more packets than it has buffers; for every route, the packets in transit between its source and destination do not exceed the window size; and no legal move is possible: no route can start a new packet (its window is full or its source has no free buffer), no packet is at the last vertex of its route, and no packet can advance, because the next vertex of its route has no free buffer.
