# Enumerated lists over distinct variables are recovered from lookups

Under `vs.Nodup`, an enumerated association list is recovered from its
lookup function: there is no duplicate key for `getVal` to shadow, so
the list is exactly the association list built from its own lookups.
