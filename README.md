Authors:
  Travis Hance (thance)
  Katherine Cordwell (kcordwell)

We prove various combinatorial identities.
In particular,

 - we start Vandermonde's identity (Katherine's focus)
 - the Hockeystick identity (Katherine's focus)
 - the catalan identity: that the catalan numbers, as defined
    by the usual recurrence, equals (1/(n+1))*(2n+1 choose n). (Travis's focus)

For some or all of these, we will use combinatorial bijections.

ORGANIZATION:
    - identities.lean (both Travis and Katherine's focus):
        - Theorems about set bijections
        - Proof that the set of lists of length n with k
          distinguished items has size (n choose k).
    - hockeystick.lean:
        - Proof of hockeystick identity and progress on Vandermonde's identity
    - catalan.lean
        - Definition of catalan numbers by recurrence
        - Proof that catalan numbers are (2n+1 choose n) / (2n+1)

