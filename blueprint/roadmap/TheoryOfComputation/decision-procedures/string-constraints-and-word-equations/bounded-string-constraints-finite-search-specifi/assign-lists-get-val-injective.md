# Enumerated lists over distinct variables give distinct assignments

Under `vs.Nodup`, distinct enumerated association lists denote
distinct assignments: if two enumerated lists agree as lookup functions
on `vs`, they are the same list. Without `Nodup` this fails, since a
duplicate key lets a later entry be shadowed by an earlier one.
