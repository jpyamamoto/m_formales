------------------------------ MODULE FindMax ------------------------------
EXTENDS Sequences, Naturals, Integers, TLAPS


(**************************************************************************)
(*                                                                        *)
(*                            Especificación                              *)
(*                                                                        *)
(**************************************************************************)


(*--fair algorithm Highest
variables
    array \in Seq(Nat);
    result = -1;
    index = 1;

define
    Max(a, b) == IF a >= b THEN a ELSE b

    TypeOK ==
        /\ array \in Seq(Nat)
        /\ index \in 1..(Len(array) + 1)
        /\ index \in Nat
        /\ result \in Nat \cup {-1}

    InductiveInvariant ==
        \A i \in 1..(index - 1) : array[i] <= result

    DoneIndexPos == pc = "Done" => index = Len(array) + 1

    Correctness ==
        pc = "Done" => \A i \in DOMAIN array : array[i] <= result
end define;

begin
    Iterate:
        while (index <= Len(array)) do
            result := Max(result, array[index]);
            index := index + 1;
        end while;
end algorithm;
*)

\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "89032e9")
VARIABLES array, result, index, pc

(* define statement *)
Max(a, b) == IF a >= b THEN a ELSE b

TypeOK ==
    /\ array \in Seq(Nat)
    /\ index \in 1..(Len(array) + 1)
    /\ index \in Nat
    /\ result \in Nat \cup {-1}

InductiveInvariant ==
    \A i \in 1..(index - 1) : array[i] <= result

DoneIndexPos == pc = "Done" => index = Len(array) + 1

Correctness ==
    pc = "Done" => \A i \in DOMAIN array : array[i] <= result


vars == << array, result, index, pc >>

Init == (* Global variables *)
        /\ array \in Seq(Nat)
        /\ result = -1
        /\ index = 1
        /\ pc = "Iterate"

Iterate == /\ pc = "Iterate"
           /\ IF (index <= Len(array))
                 THEN /\ result' = Max(result, array[index])
                      /\ index' = index + 1
                      /\ pc' = "Iterate"
                 ELSE /\ pc' = "Done"
                      /\ UNCHANGED << result, index >>
           /\ array' = array

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Iterate
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION


(**************************************************************************)
(*                                                                        *)
(*                        Verificación de Modelos                         *)
(*                                                                        *)
(**************************************************************************)


CONSTANTS MaxLength, MaxNat
ASSUME MaxLength \in Nat
ASSUME MaxNat \in Nat

MCConstraint == Len(array) <= MaxLength
MCNat == 0..MaxNat
MCSeq(S) == UNION {[1..n -> S] : n \in Nat}


(**************************************************************************)
(*                                                                        *)
(*                       Demostraciones de Teoremas                       *)
(*                                                                        *)
(**************************************************************************)


THEOREM TypeInvariantHolds == Spec => []TypeOK
PROOF
    <1>a. Init => TypeOK
        BY DEFS Init, TypeOK
    <1>b. TypeOK /\ UNCHANGED vars => TypeOK'
        BY DEFS TypeOK, vars
    <1>c. TypeOK /\ Next => TypeOK'
        <2>a. TypeOK /\ Iterate => TypeOK'
            BY DEFS TypeOK, Iterate, Max
        <2>b. TypeOK /\ Terminating => TypeOK'
            BY DEFS TypeOK, Terminating, vars
        <2> QED BY <2>a, <2>b DEF Next
    <1> QED BY PTL, <1>a, <1>b, <1>c DEF Spec


THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
PROOF
    <1>a. Init => InductiveInvariant
        BY DEFS Init, InductiveInvariant
    <1>b. InductiveInvariant /\ UNCHANGED vars => InductiveInvariant'
        BY DEFS InductiveInvariant, vars
    <1>c. InductiveInvariant /\ TypeOK /\ TypeOK' /\ Next => InductiveInvariant'
        <2>a. InductiveInvariant /\ Terminating => InductiveInvariant'
            BY DEFS InductiveInvariant, Terminating, vars
        <2>b. InductiveInvariant /\ TypeOK /\ Iterate => InductiveInvariant'
            BY DEFS InductiveInvariant, TypeOK, Iterate, Max
        <2> QED BY <2>a, <2>b DEF Next
    <1> QED BY PTL, <1>a, <1>b, <1>c, TypeInvariantHolds DEF Spec


THEOREM DoneIndexPosTheorem == Spec => []DoneIndexPos
PROOF
  <1>a. Init => DoneIndexPos
    BY DEF Init, DoneIndexPos
  <1>b. DoneIndexPos /\ UNCHANGED vars => DoneIndexPos'
    BY DEFS DoneIndexPos, vars
  <1>c. DoneIndexPos /\ TypeOK /\ Next => DoneIndexPos'
    <2>a. DoneIndexPos /\ Terminating => DoneIndexPos'
      BY DEFS DoneIndexPos, Terminating, vars
    <2>b. DoneIndexPos /\ TypeOK /\ Iterate => DoneIndexPos'
      BY DEFS DoneIndexPos, TypeOK, Iterate
    <2> QED BY <2>a, <2>b DEF Next
  <1> QED BY PTL, <1>a, <1>b, <1>c, TypeInvariantHolds DEF Spec


THEOREM IsCorrect == Spec => []Correctness
PROOF
  <1>a. Init => Correctness
    BY DEF Init, Correctness
  <1>b. Correctness /\ UNCHANGED vars => Correctness'
    BY DEF Correctness, vars
  <1>c. /\ Correctness
        /\ InductiveInvariant'
        /\ DoneIndexPos'
        /\ Next
        => Correctness'
    <2>a. Correctness /\ Terminating => Correctness'
      BY DEF Correctness, Terminating, vars
    <2>b.
        /\ Correctness
        /\ InductiveInvariant'
        /\ DoneIndexPos'
        /\ Iterate
        => Correctness'
      BY DEFS Correctness, InductiveInvariant, DoneIndexPos, Iterate
    <2> QED BY <2>a, <2>b DEF Next
  <1> QED
    BY
      <1>a, <1>b, <1>c,
      InductiveInvariantHolds, DoneIndexPosTheorem, PTL
    DEF Spec

=============================================================================
\* Modification History
\* Last modified Mon Dec 11 20:43:22 CST 2023 by jpyamamoto
\* Created Mon Dec 11 13:48:47 CST 2023 by jpyamamoto
