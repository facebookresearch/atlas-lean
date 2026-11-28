# Decoding a network node

The node decoder reads, from the front of a bit string, the number of parents in unary, that many
parent indices in unary, the number of table rows in unary, and that many rows. It returns the node
(its parent list and its rows) together with the unread suffix, and fails when any of these parts
cannot be read.
