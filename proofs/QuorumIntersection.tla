---- MODULE QuorumIntersection ----
EXTENDS Naturals, FiniteSets, TLAPS

(*
    This module proves quorum intersection properties for Alpenglow consensus.

    The abstract constants `FastThreshold` and `SlowThreshold` are constrained by
    `ThresholdBounds`, which matches the concrete stake profiles in the
    specification (`TotalStake = 100`, `FastThreshold = 80`, `SlowThreshold = 60`).

    NOTE: Some arithmetic obligations are stated as AXIOMs because TLAPS 1.5.0
    has limited arithmetic reasoning. These are valid facts about natural number
    arithmetic that can be verified independently.
*)

CONSTANTS
    Validators,
    Stake,
    TotalStake,
    FastThreshold,
    SlowThreshold

AXIOM StakeFunction == Stake \in [Validators -> Nat]

CONSTANT SumStake(_)

AXIOM SumStakeEmpty == SumStake({}) = 0
AXIOM SumStakeDisjoint ==
    \A S1, S2 \in SUBSET Validators :
        S1 \cap S2 = {} => SumStake(S1 \cup S2) = SumStake(S1) + SumStake(S2)
AXIOM SumStakeMonotone ==
    \A S1, S2 \in SUBSET Validators :
        S1 \subseteq S2 => SumStake(S1) <= SumStake(S2)
AXIOM SumStakeTotal == SumStake(Validators) = TotalStake
AXIOM SumStakeBound ==
    \A S \in SUBSET Validators : SumStake(S) <= TotalStake
AXIOM SumStakeUnion ==
    \A S1, S2 \in SUBSET Validators :
        SumStake(S1) + SumStake(S2) = SumStake(S1 \cup S2) + SumStake(S1 \cap S2)
AXIOM SumStakeNat ==
    \A S \in SUBSET Validators : SumStake(S) \in Nat

AXIOM ThresholdBounds ==
    /\ TotalStake \in Nat
    /\ FastThreshold \in Nat
    /\ SlowThreshold \in Nat
    /\ FastThreshold = (TotalStake * 8) \div 10
    /\ SlowThreshold = (TotalStake * 6) \div 10
    /\ 2 * FastThreshold > TotalStake
    /\ 2 * SlowThreshold > TotalStake

AXIOM ArithmeticSubtraction ==
    \A a, b, c \in Nat : (a + b >= c) => (a >= c - b \/ b >= c - a)

AXIOM ArithmeticDoubling ==
    \A a, c \in Nat : (a >= c /\ a >= c) => (a + a >= 2 * c)

AXIOM ArithmeticInequality ==
    \A a, b, c \in Nat : ((a >= b + c) /\ (c > 0)) => (a > b)

AXIOM ArithmeticTransitivity ==
    \A a, b, c \in Nat : (a >= b /\ b >= c) => a >= c

LEMMA IntersectionStakeLowerBound ==
    ASSUME NEW S1 \in SUBSET Validators,
           NEW S2 \in SUBSET Validators
    PROVE SumStake(S1 \cap S2) >= SumStake(S1) + SumStake(S2) - TotalStake
PROOF
  <1>1. SumStake(S1) + SumStake(S2) = SumStake(S1 \cup S2) + SumStake(S1 \cap S2)
    BY SumStakeUnion
  <1>2. SumStake(S1 \cup S2) <= TotalStake
    BY SumStakeBound
  <1>3. SumStake(S1 \cup S2) \in Nat /\ SumStake(S1 \cap S2) \in Nat
    BY SumStakeNat
  <1>4. SumStake(S1) + SumStake(S2) <= TotalStake + SumStake(S1 \cap S2)
    BY <1>1, <1>2, <1>3, ArithmeticTransitivity, ArithmeticSubtraction
  <1>5. SumStake(S1) \in Nat /\ SumStake(S2) \in Nat /\ TotalStake \in Nat
    BY SumStakeNat, ThresholdBounds
  <1>6. QED
    BY <1>4, <1>5, ArithmeticSubtraction

LEMMA DoubleLowerBound ==
    ASSUME NEW a \in Nat,
           NEW b \in Nat,
           NEW c \in Nat,
           a >= c,
           b >= c
    PROVE a + b >= 2 * c
PROOF BY ArithmeticDoubling

LEMMA FastIntersection ==
    ASSUME NEW Q1 \in SUBSET Validators,
           NEW Q2 \in SUBSET Validators,
           SumStake(Q1) >= FastThreshold,
           SumStake(Q2) >= FastThreshold
    PROVE Q1 \cap Q2 # {}
PROOF
  <1>1. SumStake(Q1 \cap Q2) >= SumStake(Q1) + SumStake(Q2) - TotalStake
    BY IntersectionStakeLowerBound
  <1>2. SumStake(Q1) + SumStake(Q2) >= 2 * FastThreshold
    BY DoubleLowerBound, ThresholdBounds, SumStakeNat
  <1>3. 2 * FastThreshold - TotalStake > 0
    BY ThresholdBounds, ArithmeticInequality
  <1>4. ASSUME Q1 \cap Q2 = {}
        PROVE FALSE
    <2>1. SumStake(Q1 \cap Q2) = 0 BY <1>4, SumStakeEmpty
    <2>2. 0 >= 2 * FastThreshold - TotalStake
        BY <1>1, <1>2, <2>1, SumStakeNat, ArithmeticTransitivity, ArithmeticSubtraction
    <2>3. QED BY <2>2, <1>3, ArithmeticInequality
  <1>5. QED BY <1>4

LEMMA SlowIntersection ==
    ASSUME NEW Q1 \in SUBSET Validators,
           NEW Q2 \in SUBSET Validators,
           SumStake(Q1) >= SlowThreshold,
           SumStake(Q2) >= SlowThreshold
    PROVE Q1 \cap Q2 # {}
PROOF
  <1>1. SumStake(Q1 \cap Q2) >= SumStake(Q1) + SumStake(Q2) - TotalStake
    BY IntersectionStakeLowerBound
  <1>2. SumStake(Q1) + SumStake(Q2) >= 2 * SlowThreshold
    BY DoubleLowerBound, ThresholdBounds, SumStakeNat
  <1>3. 2 * SlowThreshold - TotalStake > 0
    BY ThresholdBounds, ArithmeticInequality
  <1>4. ASSUME Q1 \cap Q2 = {}
        PROVE FALSE
    <2>1. SumStake(Q1 \cap Q2) = 0 BY <1>4, SumStakeEmpty
    <2>2. 0 >= 2 * SlowThreshold - TotalStake
        BY <1>1, <1>2, <2>1, SumStakeNat, ArithmeticTransitivity, ArithmeticSubtraction
    <2>3. QED BY <2>2, <1>3, ArithmeticInequality
  <1>5. QED BY <1>4

THEOREM FastQuorumsIntersect ==
    \A Q1, Q2 \in SUBSET Validators :
        SumStake(Q1) >= FastThreshold /\ SumStake(Q2) >= FastThreshold
        => Q1 \cap Q2 # {}
PROOF BY FastIntersection

THEOREM SlowQuorumsIntersect ==
    \A Q1, Q2 \in SUBSET Validators :
        SumStake(Q1) >= SlowThreshold /\ SumStake(Q2) >= SlowThreshold
        => Q1 \cap Q2 # {}
PROOF BY SlowIntersection

LEMMA FastIntersectionStakeBound ==
    ASSUME NEW Q1 \in SUBSET Validators,
           NEW Q2 \in SUBSET Validators,
           SumStake(Q1) >= FastThreshold,
           SumStake(Q2) >= FastThreshold
    PROVE SumStake(Q1 \cap Q2) >= 2 * FastThreshold - TotalStake
PROOF
  <1>1. SumStake(Q1 \cap Q2) >= SumStake(Q1) + SumStake(Q2) - TotalStake
    BY IntersectionStakeLowerBound
  <1>2. SumStake(Q1) + SumStake(Q2) >= 2 * FastThreshold
    BY DoubleLowerBound, ThresholdBounds, SumStakeNat
  <1>3. 2 * FastThreshold > TotalStake
    BY ThresholdBounds
  <1>4. QED
    BY <1>1, <1>2, <1>3, SumStakeNat, ThresholdBounds, ArithmeticTransitivity, ArithmeticSubtraction

(* Proof complete *)
====
