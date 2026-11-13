# Embedded frame counter preserves caller stacks

Embedded counting preserves every caller stack outside its
workspace on success and failure. Scratch is empty on success.
