# Decoding a fixed number of items

Given a decoder that reads one item from the front of a bit string and returns it with the unread rest (or fails), decoding $n$ items reads $n$ items one after another and returns them in order with the unread suffix; it fails if any of the $n$ reads fails, and for $n = 0$ it returns no items and the whole input.
