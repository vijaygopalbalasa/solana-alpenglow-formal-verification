---- MODULE CertificateUniqueness ----
EXTENDS QuorumIntersection

CONSTANTS
    Slots,
    Signers(_, _),
    ByzantineSet,
    ByzantineThreshold

AXIOM SignersWithinValidators ==
    \A slot \in Slots, block \in Nat : Signers(slot, block) \subseteq Validators

AXIOM HonestSingleVote ==
    \A slot \in Slots, b1, b2 \in Nat :
        b1 # b2 => (Signers(slot, b1) \cap Signers(slot, b2)) \subseteq ByzantineSet

AXIOM ByzantineSubset == ByzantineSet \subseteq Validators
AXIOM ByzantineStakeLimit == SumStake(ByzantineSet) <= ByzantineThreshold
AXIOM ByzantineThresholdBound == ByzantineThreshold = (TotalStake * 2) \div 10

THEOREM FastCertificateUnique ==
    ASSUME NEW slot \in Slots,
           NEW block1 \in Nat,
           NEW block2 \in Nat,
           block1 # block2,
           SumStake(Signers(slot, block1)) >= FastThreshold,
           SumStake(Signers(slot, block2)) >= FastThreshold
    PROVE FALSE
PROOF
  <1>1. Signers(slot, block1) \cap Signers(slot, block2) \subseteq ByzantineSet
    BY HonestSingleVote
  <1>2. Signers(slot, block1) \in SUBSET Validators /\ Signers(slot, block2) \in SUBSET Validators
    BY SignersWithinValidators
  <1>3. SumStake(ByzantineSet) >= 2 * FastThreshold - TotalStake
    BY <1>1, <1>2, ByzantineSubset, FastByzantineStakeLowerBound
  <1>4. SumStake(ByzantineSet) <= ByzantineThreshold
    BY ByzantineStakeLimit
  <1>5. 2 * FastThreshold - TotalStake > ByzantineThreshold
    BY ThresholdBounds, ByzantineThresholdBound, FastMarginStrict
  <1>6. SumStake(ByzantineSet) \in Nat /\ ByzantineThreshold \in Nat /\ 2 * FastThreshold - TotalStake \in Nat
    BY ByzantineSubset, SumStakeNat, ThresholdBounds, ByzantineThresholdBound
  <1>7. FALSE
    BY <1>3, <1>4, <1>5, <1>6, InequalityContradiction
  <1>8. QED BY <1>7

(* Proof complete *)
====
