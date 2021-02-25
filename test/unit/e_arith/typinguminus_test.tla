---- MODULE typinguminus_test ----

EXTENDS TLAPS, Integers

THEOREM ASSUME NEW n \in Int
        PROVE (-n) \in Int
    OBVIOUS

====
