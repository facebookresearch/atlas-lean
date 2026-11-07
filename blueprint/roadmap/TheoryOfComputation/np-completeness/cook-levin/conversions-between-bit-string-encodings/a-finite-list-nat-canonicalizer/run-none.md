# List canonicalizer fails on malformed input

Every malformed raw List Nat input reaches the failure endpoint.
The accumulator and Nat output may contain partial data; clear the
workspace before reuse. No output claim is made for a failed parse.
