---- MODULE QuorumIntersection ----
EXTENDS Naturals, FiniteSets, TLAPS

(*
    This module captures arithmetic facts for quorum intersection.  The
    abstract constants `FastThreshold` and `SlowThreshold` are constrained by
    `ThresholdBounds`, which matches the concrete stake profiles in the
    specification (`TotalStake = 100`, `FastThreshold = 80`, `SlowThreshold = 60`).
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
  <1>3. SumStake(S1) \in Nat /\ SumStake(S2) \in Nat /\ SumStake(S1 \cap S2) \in Nat /\ SumStake(S1 \cup S2) \in Nat
    BY SumStakeNat
  <1>4. QED
    BY <1>1, <1>2, <1>3

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
  <1>1. CASE Q1 \cap Q2 = {}
    <2>1. SumStake(Q1 \cup Q2) = SumStake(Q1) + SumStake(Q2)
      BY <1>1, SumStakeDisjoint
    <2>2. SumStake(Q1) + SumStake(Q2) >= 2 * FastThreshold
      BY DoubleLowerBound, ThresholdBounds, SumStakeNat
    <2>3. 2 * FastThreshold > TotalStake
      BY ThresholdBounds
    <2>4. SumStake(Q1 \cup Q2) <= TotalStake
      BY SumStakeBound
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4, SumStakeNat, ThresholdBounds
  <1>2. QED
    BY <1>1

LEMMA SlowIntersection ==
    ASSUME NEW Q1 \in SUBSET Validators,
           NEW Q2 \in SUBSET Validators,
           SumStake(Q1) >= SlowThreshold,
           SumStake(Q2) >= SlowThreshold
    PROVE Q1 \cap Q2 # {}
PROOF
  <1>1. CASE Q1 \cap Q2 = {}
    <2>1. SumStake(Q1 \cup Q2) = SumStake(Q1) + SumStake(Q2)
      BY <1>1, SumStakeDisjoint
    <2>2. SumStake(Q1) + SumStake(Q2) >= 2 * SlowThreshold
      BY DoubleLowerBound, ThresholdBounds, SumStakeNat
    <2>3. 2 * SlowThreshold > TotalStake
      BY ThresholdBounds
    <2>4. SumStake(Q1 \cup Q2) <= TotalStake
      BY SumStakeBound
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4, SumStakeNat, ThresholdBounds
  <1>2. QED
    BY <1>1

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
  <1>3. QED
    BY <1>1, <1>2, SumStakeNat, ThresholdBounds

(* Proof complete *)
====
