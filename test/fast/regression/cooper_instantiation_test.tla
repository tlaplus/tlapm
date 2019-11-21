-----------  MODULE cooper_instantiation_test ---------------
EXTENDS Integers

THEOREM SimpleArithmetic == TRUE (*{ by (cooper) }*)

THEOREM ASSUME NEW CONSTANT XXX,
        NEW CONSTANT i \in Int
        PROVE  XXX  \in  Int
BY SimpleArithmetic
====================================
stderr: status:failed
nostderr: status:proved
