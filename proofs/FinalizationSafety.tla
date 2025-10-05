---- MODULE FinalizationSafety ----
EXTENDS QuorumIntersection

CONSTANTS
    Slots,
    FastCertSigners(_,_),
    SlowCertSigners(_,_),
    FinalCertSigners(_,_),
    ByzantineSet,
    ByzantineThreshold

AXIOM FastCertWithinValidators ==
    \A slot \in Slots, block \in Nat : FastCertSigners(slot, block) \subseteq Validators

AXIOM SlowCertWithinValidators ==
    \A slot \in Slots, block \in Nat : SlowCertSigners(slot, block) \subseteq Validators

AXIOM FinalCertWithinValidators ==
    \A slot \in Slots, block \in Nat : FinalCertSigners(slot, block) \subseteq Validators

AXIOM HonestSingleVote ==
    \A slot \in Slots, b1, b2 \in Nat :
        b1 # b2 => (FinalCertSigners(slot, b1) \cap FinalCertSigners(slot, b2)) \subseteq ByzantineSet

AXIOM ByzantineSubset == ByzantineSet \subseteq Validators
AXIOM ByzantineStakeLimit == SumStake(ByzantineSet) <= ByzantineThreshold
AXIOM ByzantineThresholdBound == ByzantineThreshold = (TotalStake * 2) \div 10
AXIOM FastMargin == 2 * FastThreshold - TotalStake > ByzantineThreshold

THEOREM NoConflictingFastCertificates ==
    ASSUME NEW slot \in Slots,
           NEW block1 \in Nat,
           NEW block2 \in Nat,
           block1 # block2,
           SumStake(FastCertSigners(slot, block1)) >= FastThreshold,
           SumStake(FastCertSigners(slot, block2)) >= FastThreshold
    PROVE FALSE
PROOF
  <1>1. FastCertSigners(slot, block1) \in SUBSET Validators
    BY FastCertWithinValidators
  <1>2. FastCertSigners(slot, block2) \in SUBSET Validators
    BY FastCertWithinValidators
  <1>3. SumStake(FastCertSigners(slot, block1) \cap FastCertSigners(slot, block2)) >= 2 * FastThreshold - TotalStake
    BY <1>1, <1>2, FastIntersectionStakeBound
  <1>4. FastCertSigners(slot, block1) \cap FastCertSigners(slot, block2) \subseteq ByzantineSet
    BY HonestSingleVote
  <1>5. SumStake(FastCertSigners(slot, block1) \cap FastCertSigners(slot, block2)) <= ByzantineThreshold
    BY <1>3, <1>4, ByzantineSubset, ByzantineStakeLimit, SumStakeMonotone
  <1>6. 2 * FastThreshold - TotalStake > ByzantineThreshold
    BY FastMargin
  <1>7. QED
    BY <1>3, <1>5, <1>6, SumStakeNat

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
  <1>3. QED
    BY <1>1, <1>2, SumStakeNat, ThresholdBounds

THEOREM NoConflictingFinalCertificates ==
    ASSUME NEW slot \in Slots,
           NEW block1 \in Nat,
           NEW block2 \in Nat,
           block1 # block2,
           SumStake(FinalCertSigners(slot, block1)) >= SlowThreshold,
           SumStake(FinalCertSigners(slot, block2)) >= SlowThreshold
    PROVE FALSE
PROOF
  <1>1. FinalCertSigners(slot, block1) \in SUBSET Validators
    BY FinalCertWithinValidators
  <1>2. FinalCertSigners(slot, block2) \in SUBSET Validators
    BY FinalCertWithinValidators
  <1>3. FinalCertSigners(slot, block1) \cap FinalCertSigners(slot, block2) # {}
    BY <1>1, <1>2, SlowIntersection
  <1>4. FinalCertSigners(slot, block1) \cap FinalCertSigners(slot, block2) \subseteq ByzantineSet
    BY HonestSingleVote
  <1>5. SumStake(FinalCertSigners(slot, block1) \cap FinalCertSigners(slot, block2)) >= 2 * SlowThreshold - TotalStake
    BY <1>1, <1>2, SlowIntersectionStakeBound
  <1>6. SumStake(FinalCertSigners(slot, block1) \cap FinalCertSigners(slot, block2)) <= ByzantineThreshold
    BY <1>4, ByzantineSubset, ByzantineStakeLimit, SumStakeMonotone
  <1>7. 2 * SlowThreshold - TotalStake > ByzantineThreshold
    BY ThresholdBounds
  <1>8. QED
    BY <1>5, <1>6, <1>7, SumStakeNat

(* Proof complete *)
====
