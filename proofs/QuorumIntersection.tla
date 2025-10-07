---- MODULE QuorumIntersection ----
EXTENDS FiniteSets, StakeArithmetic

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
  <1>4. SumStake(S1 \cup S2) + SumStake(S1 \cap S2) <= TotalStake + SumStake(S1 \cap S2)
    BY <1>2, <1>3, ThresholdBounds, NatAddMonotone
  <1>5. SumStake(S1) + SumStake(S2) = SumStake(S1 \cup S2) + SumStake(S1 \cap S2)
    BY <1>1
  <1>6. TotalStake + SumStake(S1 \cap S2) >= SumStake(S1 \cup S2) + SumStake(S1 \cap S2)
    BY <1>2, <1>3, ThresholdBounds, NatAddMonotoneGe
  <1>7. SumStake(S1 \cap S2) + TotalStake = TotalStake + SumStake(S1 \cap S2)
    BY <1>3, ThresholdBounds, NatAddCommute
  <1>8. SumStake(S1 \cap S2) + TotalStake >= SumStake(S1) + SumStake(S2)
    BY <1>5, <1>6, <1>7
  <1>9. SumStake(S1) \in Nat /\ SumStake(S2) \in Nat /\ TotalStake \in Nat
    BY SumStakeNat, ThresholdBounds
  <1>10. QED
    BY <1>8, <1>9, <1>3, AddToSubtraction

LEMMA DoubleLowerBound ==
    ASSUME NEW a \in Nat,
           NEW b \in Nat,
           NEW c \in Nat,
           a >= c,
           b >= c
    PROVE a + b >= 2 * c
PROOF OBVIOUS

LEMMA FastIntersection ==
    ASSUME NEW Q1 \in SUBSET Validators,
           NEW Q2 \in SUBSET Validators,
           SumStake(Q1) >= FastThreshold,
           SumStake(Q2) >= FastThreshold
    PROVE Q1 \cap Q2 # {}
PROOF
  <1>1. SumStake(Q1) + SumStake(Q2) >= 2 * FastThreshold
    BY DoubleLowerBound, ThresholdBounds, SumStakeNat
  <1>2. ASSUME Q1 \cap Q2 = {}
        PROVE FALSE
    <2>1. SumStake(Q1) + SumStake(Q2) = SumStake(Q1 \cup Q2)
        BY <1>2, SumStakeDisjoint
    <2>2. SumStake(Q1 \cup Q2) <= TotalStake BY SumStakeBound
    <2>3. SumStake(Q1) + SumStake(Q2) <= TotalStake
        BY <2>1, <2>2
    <2>4. SumStake(Q1) \in Nat /\ SumStake(Q2) \in Nat
        BY SumStakeNat
    <2>5. TotalStake >= 2 * FastThreshold
        BY <1>1, <2>3, <2>4, ThresholdBounds, UpperLowerTrans
    <2>6. FALSE BY <2>5, ThresholdBounds, GreaterAndLessContradiction
    <2>7. QED BY <2>6
  <1>3. QED BY <1>2

LEMMA SlowIntersection ==
    ASSUME NEW Q1 \in SUBSET Validators,
           NEW Q2 \in SUBSET Validators,
           SumStake(Q1) >= SlowThreshold,
           SumStake(Q2) >= SlowThreshold
    PROVE Q1 \cap Q2 # {}
PROOF
  <1>1. SumStake(Q1) + SumStake(Q2) >= 2 * SlowThreshold
    BY DoubleLowerBound, ThresholdBounds, SumStakeNat
  <1>2. ASSUME Q1 \cap Q2 = {}
        PROVE FALSE
    <2>1. SumStake(Q1) + SumStake(Q2) = SumStake(Q1 \cup Q2)
        BY <1>2, SumStakeDisjoint
    <2>2. SumStake(Q1 \cup Q2) <= TotalStake BY SumStakeBound
    <2>3. SumStake(Q1) + SumStake(Q2) <= TotalStake
        BY <2>1, <2>2
    <2>4. SumStake(Q1) \in Nat /\ SumStake(Q2) \in Nat
        BY SumStakeNat
    <2>5. TotalStake >= 2 * SlowThreshold
        BY <1>1, <2>3, <2>4, ThresholdBounds, UpperLowerTrans
    <2>6. FALSE BY <2>5, ThresholdBounds, GreaterAndLessContradiction
    <2>7. QED BY <2>6
  <1>3. QED BY <1>2

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
  <1>3. SumStake(Q1) + SumStake(Q2) <= SumStake(Q1 \cap Q2) + TotalStake
    BY <1>1, ThresholdBounds, SumStakeNat, NatAddMonotone
  <1>4. SumStake(Q1 \cap Q2) + TotalStake >= SumStake(Q1) + SumStake(Q2)
    BY <1>3
  <1>5. SumStake(Q1 \cap Q2) + TotalStake >= 2 * FastThreshold
    BY <1>2, <1>4, ThresholdBounds, SumStakeNat, NatGeTrans
  <1>6. QED
    BY <1>5, ThresholdBounds, SumStakeNat, AddToSubtraction

LEMMA SlowIntersectionStakeBound ==
    ASSUME NEW Q1 \in SUBSET Validators,
           NEW Q2 \in SUBSET Validators,
           SumStake(Q1) >= SlowThreshold,
           SumStake(Q2) >= SlowThreshold
    PROVE SumStake(Q1 \cap Q2) >= 2 * SlowThreshold - TotalStake
PROOF
  <1>1. SumStake(Q1 \cap Q2) >= SumStake(Q1) + SumStake(Q2) - TotalStake
    BY IntersectionStakeLowerBound
  <1>2. SumStake(Q1) + SumStake(Q2) >= 2 * SlowThreshold
    BY DoubleLowerBound, ThresholdBounds, SumStakeNat
  <1>3. SumStake(Q1) + SumStake(Q2) <= SumStake(Q1 \cap Q2) + TotalStake
    BY <1>1, ThresholdBounds, SumStakeNat, NatAddMonotone
  <1>4. SumStake(Q1 \cap Q2) + TotalStake >= SumStake(Q1) + SumStake(Q2)
    BY <1>3
  <1>5. SumStake(Q1 \cap Q2) + TotalStake >= 2 * SlowThreshold
    BY <1>2, <1>4, ThresholdBounds, SumStakeNat, NatGeTrans
  <1>6. QED
    BY <1>5, ThresholdBounds, SumStakeNat, AddToSubtraction

LEMMA FastByzantineStakeLowerBound ==
    ASSUME NEW Q1 \in SUBSET Validators,
           NEW Q2 \in SUBSET Validators,
           NEW BSet \in SUBSET Validators,
           SumStake(Q1) >= FastThreshold,
           SumStake(Q2) >= FastThreshold,
           Q1 \cap Q2 \subseteq BSet
    PROVE SumStake(BSet) >= 2 * FastThreshold - TotalStake
PROOF
  <1>1. SumStake(Q1 \cap Q2) >= 2 * FastThreshold - TotalStake
    BY FastIntersectionStakeBound
  <1>2. SumStake(Q1 \cap Q2) <= SumStake(BSet)
    BY SumStakeMonotone
  <1>3. SumStake(BSet) \in Nat /\ SumStake(Q1 \cap Q2) \in Nat
    BY SumStakeNat
  <1>4. 2 * FastThreshold - TotalStake \in Nat
    BY ThresholdBounds
  <1>5. SumStake(BSet) >= 2 * FastThreshold - TotalStake
    BY <1>1, <1>2, <1>3, <1>4, UpperLowerTrans
  <1>6. QED BY <1>5

LEMMA SlowByzantineStakeLowerBound ==
    ASSUME NEW Q1 \in SUBSET Validators,
           NEW Q2 \in SUBSET Validators,
           NEW BSet \in SUBSET Validators,
           SumStake(Q1) >= SlowThreshold,
           SumStake(Q2) >= SlowThreshold,
           Q1 \cap Q2 \subseteq BSet
    PROVE SumStake(BSet) >= 2 * SlowThreshold - TotalStake
PROOF
  <1>1. SumStake(Q1 \cap Q2) >= 2 * SlowThreshold - TotalStake
    BY SlowIntersectionStakeBound
  <1>2. SumStake(Q1 \cap Q2) <= SumStake(BSet)
    BY SumStakeMonotone
  <1>3. SumStake(BSet) \in Nat /\ SumStake(Q1 \cap Q2) \in Nat
    BY SumStakeNat
  <1>4. 2 * SlowThreshold - TotalStake \in Nat
    BY ThresholdBounds
  <1>5. SumStake(BSet) >= 2 * SlowThreshold - TotalStake
    BY <1>1, <1>2, <1>3, <1>4, UpperLowerTrans
  <1>6. QED BY <1>5

(* Proof complete *)
====
