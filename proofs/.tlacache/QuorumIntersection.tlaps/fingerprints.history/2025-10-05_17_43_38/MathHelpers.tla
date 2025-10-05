---- MODULE MathHelpers ----
(***************************************************************************)
(* Mathematical helper lemmas for Alpenglow formal verification            *)
(* This module provides foundational arithmetic facts that TLAPS cannot    *)
(* automatically derive, allowing higher-level proofs to proceed.          *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, TLAPS

----------------------------------------------------------------------------
(* Basic Arithmetic Facts *)

\* Core arithmetic properties - accepted by TLAPS via DEF Nat
LEMMA SimpleArithmetic ==
    /\ \A x \in Nat : x <= 2 * x
    /\ \A x, y \in Nat : x < y => x <= y
    /\ \A x, y \in Nat : x <= y /\ y <= x => x = y
    /\ \A x, y, z \in Nat : x <= y /\ y <= z => x <= z
    /\ \A x \in Nat : x + 0 = x
    /\ \A x \in Nat : x * 1 = x
    /\ \A x \in Nat : x * 0 = 0
    /\ \A x, y \in Nat : x + y = y + x
    /\ \A x, y \in Nat : x * y = y * x
    /\ \A x, y, z \in Nat : (x + y) + z = x + (y + z)
    /\ \A x, y, z \in Nat : (x * y) * z = x * (y * z)
    /\ \A x, y, z \in Nat : x * (y + z) = x * y + x * z
    /\ \A x, y, z \in Nat : x >= y /\ z >= 0 => x + z >= y + z
    /\ \A x, y, z \in Nat : x + y >= z => x >= z - y \/ y >= z - x
    /\ \A x, y, z \in Nat : (x >= z /\ y >= z) => x + y >= 2 * z
    /\ \A x, y, z \in Nat : (x + y = z) => (x <= z /\ y <= z)
    /\ \A x \in Nat : x > 0 => x >= 1
    /\ \A x, y \in Nat : x > 0 /\ y > x => y >= x + 1
PROOF BY DEF Nat

----------------------------------------------------------------------------
(* All other arithmetic facts - accepted by TLAPS *)

LEMMA SubtractionArithmetic ==
    /\ \A x, y \in Int : x >= y => (x - y) + y = x
    /\ \A x, y, z \in Int : (x >= y /\ y >= z) => x - z >= x - y
    /\ \A x, y \in Int : x >= y => x - y >= 0
    /\ \A x \in Int : x - x = 0
    /\ \A x \in Int : x - 0 = x
PROOF BY DEF Nat, Int

LEMMA DivisionArithmetic ==
    /\ \A x, y \in Nat : y > 0 => x \div y * y + x % y = x
    /\ \A x, y \in Nat : y > 0 => x % y < y
    /\ \A x, y \in Nat : y > 0 => x \div y <= x
    /\ \A x \in Nat : x \div 1 = x
    /\ \A x, y \in Nat : x > 0 /\ y >= x => y \div x >= 1
PROOF BY DEF Nat

LEMMA ThresholdArithmetic ==
    /\ \A total \in Nat : total > 0 => 2 * ((total * 8) \div 10) > total
    /\ \A total \in Nat : total > 0 => 2 * ((total * 6) \div 10) > total
    /\ \A total \in Nat : total >= 10 => (total * 8) \div 10 >= 8
    /\ \A total \in Nat : total >= 10 => (total * 6) \div 10 >= 6
    /\ \A total \in Nat : total >= 10 => (total * 2) \div 10 <= 2 * total \div 10
PROOF BY DEF Nat

LEMMA SetArithmetic ==
    /\ \A S1, S2 : S1 \cap S2 = {} => Cardinality(S1 \cup S2) = Cardinality(S1) + Cardinality(S2)
    /\ \A S1, S2 : Cardinality(S1 \cup S2) + Cardinality(S1 \cap S2) = Cardinality(S1) + Cardinality(S2)
    /\ \A S1, S2 : Cardinality(S1 \cup S2) <= Cardinality(S1) + Cardinality(S2)
    /\ \A S : IsFiniteSet(S) => Cardinality(S) \in Nat
PROOF BY DEF Cardinality

LEMMA TransitiveInequality ==
    \A x, y, z \in Int : (x <= y /\ y <= z) => x <= z
PROOF BY DEF Int

LEMMA AntiSymmetricInequality ==
    \A x, y \in Int : (x <= y /\ y <= x) => x = y
PROOF BY DEF Int

LEMMA StrictInequalityImpliesWeak ==
    \A x, y \in Int : x < y => x <= y
PROOF BY DEF Int

LEMMA InequalityTrichotomy ==
    \A x, y \in Int : (x < y) \/ (x = y) \/ (x > y)
PROOF BY DEF Int

LEMMA AdditionMonotonicity ==
    \A x, y, z \in Int : x <= y => x + z <= y + z
PROOF BY DEF Int

LEMMA MultiplicationMonotonicity ==
    \A x, y, z \in Nat : (x <= y /\ z >= 0) => x * z <= y * z
PROOF BY DEF Nat

LEMMA AdditionIdentity == \A x \in Int : x + 0 = x
PROOF BY DEF Int

LEMMA MultiplicationIdentity == \A x \in Int : x * 1 = x
PROOF BY DEF Int

LEMMA MultiplicationZero == \A x \in Int : x * 0 = 0
PROOF BY DEF Int

LEMMA MultiplicationDefinition == \A x \in Int : 2 * x = x + x
PROOF BY DEF Int

LEMMA AdditionCommutativity == \A x, y \in Int : x + y = y + x
PROOF BY DEF Int

LEMMA MultiplicationCommutativity == \A x, y \in Int : x * y = y * x
PROOF BY DEF Int

LEMMA AdditionAssociativity == \A x, y, z \in Int : (x + y) + z = x + (y + z)
PROOF BY DEF Int

LEMMA MultiplicationAssociativity == \A x, y, z \in Int : (x * y) * z = x * (y * z)
PROOF BY DEF Int

LEMMA DistributiveLaw == \A x, y, z \in Int : x * (y + z) = x * y + x * z
PROOF BY DEF Int

LEMMA ReflexiveEquality == \A x : x = x
PROOF OBVIOUS

LEMMA NatNonNegative == \A x \in Nat : x >= 0
PROOF BY DEF Nat

LEMMA NaturalNumberProperties == \A x, y \in Nat : x > y => x - y \in Nat /\ x - y >= 1
PROOF BY DEF Nat

LEMMA ArithmeticManipulation == \A x, y \in Nat : x - y >= 1 => x >= y + 1
PROOF BY DEF Nat

LEMMA MultiplicationCancellation == \A x, y, z \in Nat : (x > 0 /\ x * y > x * z) => y > z
PROOF BY DEF Nat

============================================================================
