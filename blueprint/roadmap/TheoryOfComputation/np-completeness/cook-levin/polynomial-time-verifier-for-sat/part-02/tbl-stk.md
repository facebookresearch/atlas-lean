# Table stack of an entry list

Write each table entry as one bit symbol per bit of its
name followed by its closing marker (the value symbol for its value, or the dead symbol if it
has no value), and concatenate these in the order of the list. The table stack is the reverse
of this sequence, with the head as the top of the stack, so the first entry lies at the bottom.
