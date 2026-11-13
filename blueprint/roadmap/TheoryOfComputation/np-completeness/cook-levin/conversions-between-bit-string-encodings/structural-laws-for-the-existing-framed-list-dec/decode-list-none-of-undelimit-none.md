# Malformed first frame makes list decoding fail

A nonempty input with a malformed first frame fails list decoding.
Empty input is excluded because it is the valid empty list.
