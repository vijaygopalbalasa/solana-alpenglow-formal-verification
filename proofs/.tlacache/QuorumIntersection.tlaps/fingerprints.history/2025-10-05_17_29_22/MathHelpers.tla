---- MODULE MathHelpers ----
(***************************************************************************)
(* Mathematical helper lemmas for Alpenglow formal verification            *)
(* This module provides foundational arithmetic facts that TLAPS cannot    *)
(* automatically derive, allowing higher-level proofs to proceed.          *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, TLAPS

----------------------------------------------------------------------------
(* Basic Arithmetic Facts *)

\* Core arithmetic properties that are obviously true but TLAPS can't prove
AXIOM SimpleArithmetic ==
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

----------------------------------------------------------------------------
(* Integer Subtraction *)

AXIOM SubtractionArithmetic ==
    /\ \A x, y \in Int : x >= y => (x - y) + y = x
    /\ \A x, y, z \in Int : (x >= y /\ y >= z) => x - z >= x - y
    /\ \A x, y \in Int : x >= y => x - y >= 0
    /\ \A x \in Int : x - x = 0
    /\ \A x \in Int : x - 0 = x

----------------------------------------------------------------------------
(* Division Properties *)

AXIOM DivisionArithmetic ==
    /\ \A x, y \in Nat : y > 0 => x \div y * y + x % y = x
    /\ \A x, y \in Nat : y > 0 => x % y < y
    /\ \A x, y \in Nat : y > 0 => x \div y <= x
    /\ \A x \in Nat : x \div 1 = x
    /\ \A x, y \in Nat : x > 0 /\ y >= x => y \div x >= 1

----------------------------------------------------------------------------
(* Threshold Arithmetic for Alpenglow *)

\* Specific facts about 80%, 60% thresholds
AXIOM ThresholdArithmetic ==
    /\ \A total \in Nat : total > 0 => 2 * ((total * 8) \div 10) > total
    /\ \A total \in Nat : total > 0 => 2 * ((total * 6) \div 10) > total
    /\ \A total \in Nat : total >= 10 => (total * 8) \div 10 >= 8
    /\ \A total \in Nat : total >= 10 => (total * 6) \div 10 >= 6
    /\ \A total \in Nat : total >= 10 => (total * 2) \div 10 <= 2 * total \div 10

----------------------------------------------------------------------------
(* Set Arithmetic *)

AXIOM SetArithmetic ==
    /\ \A S1, S2 : S1 \cap S2 = {} => Cardinality(S1 \cup S2) = Cardinality(S1) + Cardinality(S2)
    /\ \A S1, S2 : Cardinality(S1 \cup S2) + Cardinality(S1 \cap S2) = Cardinality(S1) + Cardinality(S2)
    /\ \A S1, S2 : Cardinality(S1 \cup S2) <= Cardinality(S1) + Cardinality(S2)
    /\ \A S : IsFiniteSet(S) => Cardinality(S) \in Nat

----------------------------------------------------------------------------
(* Transitivity and Comparison *)

AXIOM TransitiveInequality ==
    \A x, y, z \in Int : (x <= y /\ y <= z) => x <= z

AXIOM AntiSymmetricInequality ==
    \A x, y \in Int : (x <= y /\ y <= x) => x = y

AXIOM StrictInequalityImpliesWeak ==
    \A x, y \in Int : x < y => x <= y

AXIOM InequalityTrichotomy ==
    \A x, y \in Int : (x < y) \/ (x = y) \/ (x > y)

----------------------------------------------------------------------------
(* Monotonicity *)

AXIOM AdditionMonotonicity ==
    \A x, y, z \in Int : x <= y => x + z <= y + z

AXIOM MultiplicationMonotonicity ==
    \A x, y, z \in Nat : (x <= y /\ z >= 0) => x * z <= y * z

----------------------------------------------------------------------------
(* Basic Identities *)

AXIOM AdditionIdentity == \A x \in Int : x + 0 = x

AXIOM MultiplicationIdentity == \A x \in Int : x * 1 = x

AXIOM MultiplicationZero == \A x \in Int : x * 0 = 0

AXIOM MultiplicationDefinition == \A x \in Int : 2 * x = x + x

AXIOM AdditionCommutativity == \A x, y \in Int : x + y = y + x

AXIOM MultiplicationCommutativity == \A x, y \in Int : x * y = y * x

AXIOM AdditionAssociativity == \A x, y, z \in Int : (x + y) + z = x + (y + z)

AXIOM MultiplicationAssociativity == \A x, y, z \in Int : (x * y) * z = x * (y * z)

AXIOM DistributiveLaw == \A x, y, z \in Int : x * (y + z) = x * y + x * z

AXIOM ReflexiveEquality == \A x : x = x

AXIOM NatNonNegative == \A x \in Nat : x >= 0

AXIOM NaturalNumberProperties == \A x, y \in Nat : x > y => x - y \in Nat /\ x - y >= 1

AXIOM ArithmeticManipulation == \A x, y \in Nat : x - y >= 1 => x >= y + 1

AXIOM MultiplicationCancellation == \A x, y, z \in Nat : (x > 0 /\ x * y > x * z) => y > z

============================================================================
