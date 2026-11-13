# Four-output decoder fails on malformed input

Every failed raw decode reaches `bad` within the same whole-input
bound. Failed owned workspace can be partial and must be discarded
or cleared.
