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

AXIOM HonestSingleVoteFast ==
    \A slot \in Slots, b1, b2 \in Nat :
        b1 # b2 => (FastCertSigners(slot, b1) \cap FastCertSigners(slot, b2)) \subseteq ByzantineSet

AXIOM ByzantineSubset == ByzantineSet \subseteq Validators
AXIOM ByzantineStakeLimit == SumStake(ByzantineSet) <= ByzantineThreshold
AXIOM ByzantineThresholdBound == ByzantineThreshold = (TotalStake * 2) \div 10
\* Margins are derived via StakeArithmetic lemmas; avoid axioms here.

(* Local intersection lemmas removed; we use global bounds from QuorumIntersection. *)

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
  <1>3. FastCertSigners(slot, block1) \cap FastCertSigners(slot, block2) \subseteq ByzantineSet
    BY HonestSingleVoteFast
  <1>4. SumStake(ByzantineSet) >= 2 * FastThreshold - TotalStake
    BY <1>1, <1>2, <1>3, ByzantineSubset, FastByzantineStakeLowerBound
  <1>5. SumStake(ByzantineSet) <= ByzantineThreshold
    BY ByzantineStakeLimit
  <1>6. 2 * FastThreshold - TotalStake > ByzantineThreshold
    BY ThresholdBounds, ByzantineThresholdBound, FastMarginStrict
  <1>7. SumStake(ByzantineSet) \in Nat /\ ByzantineThreshold \in Nat /\ 2 * FastThreshold - TotalStake \in Nat
    BY ByzantineSubset, SumStakeNat, ThresholdBounds, ByzantineThresholdBound
  <1>8. FALSE
    BY <1>4, <1>5, <1>6, <1>7, InequalityContradiction
  <1>9. QED BY <1>8

THEOREM FinalCertByzantineStakeLowerBound ==
    ASSUME NEW slot \in Slots,
           NEW block1 \in Nat,
           NEW block2 \in Nat,
           block1 # block2,
           SumStake(FinalCertSigners(slot, block1)) >= SlowThreshold,
           SumStake(FinalCertSigners(slot, block2)) >= SlowThreshold
    PROVE SumStake(ByzantineSet) >= 2 * SlowThreshold - TotalStake
PROOF
  <1>1. FinalCertSigners(slot, block1) \in SUBSET Validators
    BY FinalCertWithinValidators
  <1>2. FinalCertSigners(slot, block2) \in SUBSET Validators
    BY FinalCertWithinValidators
  <1>3. FinalCertSigners(slot, block1) \cap FinalCertSigners(slot, block2) \subseteq ByzantineSet
    BY HonestSingleVote
  <1>4. QED
    BY <1>1, <1>2, <1>3, ByzantineSubset, SlowByzantineStakeLowerBound

(* Proof complete *)
====
