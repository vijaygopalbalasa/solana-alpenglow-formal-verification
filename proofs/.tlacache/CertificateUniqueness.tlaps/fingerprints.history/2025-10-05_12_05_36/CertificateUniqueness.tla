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
AXIOM FastMargin == 2 * FastThreshold - TotalStake > ByzantineThreshold

THEOREM FastCertificateUnique ==
    ASSUME NEW slot \in Slots,
           NEW block1 \in Nat,
           NEW block2 \in Nat,
           block1 # block2,
           SumStake(Signers(slot, block1)) >= FastThreshold,
           SumStake(Signers(slot, block2)) >= FastThreshold
    PROVE FALSE
PROOF OMITTED

====
