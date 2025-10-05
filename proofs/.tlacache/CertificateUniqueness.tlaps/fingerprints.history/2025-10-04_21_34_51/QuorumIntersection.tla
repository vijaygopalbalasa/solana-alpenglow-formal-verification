---- MODULE QuorumIntersection ----
EXTENDS Naturals, FiniteSets, TLAPS

CONSTANTS
    Validators,
    Stake,
    TotalStake

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

FastThreshold == (TotalStake * 8) \div 10
SlowThreshold == (TotalStake * 6) \div 10

LEMMA IntersectionStakeLowerBound ==
    ASSUME NEW S1 \in SUBSET Validators,
           NEW S2 \in SUBSET Validators
    PROVE SumStake(S1 \cap S2) >= SumStake(S1) + SumStake(S2) - TotalStake
PROOF
<1>1. SumStake(S1) + SumStake(S2) = SumStake(S1 \cup S2) + SumStake(S1 \cap S2)
    BY SumStakeUnion
<1>2. SumStake(S1 \cup S2) <= TotalStake
    BY SumStakeBound
<1>3. SumStake(S1 \cap S2) >= SumStake(S1) + SumStake(S2) - TotalStake
    BY <1>1, <1>2
<1> QED

LEMMA FastIntersection ==
    ASSUME NEW Q1 \in SUBSET Validators,
           NEW Q2 \in SUBSET Validators,
           SumStake(Q1) >= FastThreshold,
           SumStake(Q2) >= FastThreshold
    PROVE Q1 \cap Q2 # {}
PROOF
<1>1. CASE Q1 \cap Q2 = {}
  <2>1. SumStake(Q1 \cup Q2) = SumStake(Q1) + SumStake(Q2)
    BY SumStakeDisjoint, <1>1
  <2>2. SumStake(Q1) + SumStake(Q2) >= 2 * FastThreshold
    OBVIOUS
  <2>3. 2 * FastThreshold = (TotalStake * 16) \div 10
    BY DEF FastThreshold
  <2>4. (TotalStake * 16) \div 10 > TotalStake
    OBVIOUS
  <2>5. SumStake(Q1 \cup Q2) > TotalStake
    BY <2>1, <2>2, <2>3, <2>4
  <2>6. SumStake(Q1 \cup Q2) <= TotalStake
    BY SumStakeBound
  <2>7. FALSE
    BY <2>5, <2>6
  <2> QED
<1> QED

LEMMA SlowIntersection ==
    ASSUME NEW Q1 \in SUBSET Validators,
           NEW Q2 \in SUBSET Validators,
           SumStake(Q1) >= SlowThreshold,
           SumStake(Q2) >= SlowThreshold
    PROVE Q1 \cap Q2 # {}
PROOF
<1>1. CASE Q1 \cap Q2 = {}
  <2>1. SumStake(Q1 \cup Q2) = SumStake(Q1) + SumStake(Q2)
    BY SumStakeDisjoint, <1>1
  <2>2. SumStake(Q1) + SumStake(Q2) >= 2 * SlowThreshold
    OBVIOUS
  <2>3. 2 * SlowThreshold = (TotalStake * 12) \div 10
    BY DEF SlowThreshold
  <2>4. (TotalStake * 12) \div 10 > TotalStake
    OBVIOUS
  <2>5. SumStake(Q1 \cup Q2) > TotalStake
    BY <2>1, <2>2, <2>3, <2>4
  <2>6. SumStake(Q1 \cup Q2) <= TotalStake
    BY SumStakeBound
  <2>7. FALSE
    BY <2>5, <2>6
  <2> QED
<1> QED

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
    OBVIOUS
<1>3. SumStake(Q1 \cap Q2) >= 2 * FastThreshold - TotalStake
    BY <1>1, <1>2
<1> QED

====
