---- MODULE AlpenglowCore ----
EXTENDS Naturals, FiniteSets, Sequences

(*************************************************************************)
(* Core types and helper operators shared by the Alpenglow specifications *)
(*************************************************************************)

CONSTANTS
    StakeProfileId,    \* Identifier selecting stake/validator profile
    MaxSlot,           \* Upper bound on slots explored in the model
    WindowSize,        \* Number of concurrently open slots
    TimeoutLimit,      \* Number of ticks before triggering slow-path timeout
    K,                 \* Minimum shards required for reconstruction (K-of-N)
    NULL               \* Distinguished null value used in optional fields

StakeVector ==
    CASE StakeProfileId = "equal4" -> <<25, 25, 25, 25>>
         [] StakeProfileId = "byz5" -> <<25, 20, 20, 20, 15>>
         [] OTHER -> <<25, 25, 25, 25>>

Validators == 1..Len(StakeVector)
ValidatorCount == Len(StakeVector)

ShardUniverse ==
    IF StakeProfileId = "byz5" THEN {1,2,3,4,5,6} ELSE 1..5

ASSUME KPositive == K \in 1..Cardinality(ShardUniverse)

(*************************************************************************)
(* Basic derived operators                                                *)
(*************************************************************************)

StakeAmount(v) == IF v \in Validators THEN StakeVector[v] ELSE 0

RECURSIVE SumStake(_)
SumStake(S) == IF S = {} THEN 0
               ELSE LET v == CHOOSE x \in S : TRUE
                        remaining == S \ {v}
                    IN StakeAmount(v) + SumStake(remaining)

TotalStake == SumStake(Validators)

HasStake(S, threshold) == SumStake(S) >= threshold

FastThreshold == (TotalStake * 8) \div 10
SlowThreshold == (TotalStake * 6) \div 10
ByzantineThreshold == (TotalStake * 2) \div 10
CrashThreshold == (TotalStake * 2) \div 10

VoteKind == {"none", "fast", "fallback", "final", "skip"}
ValidatorStatus == {"online", "offline", "byzantine"}
CertificateStatus == {"none", "fast", "slow", "final", "skip"}

BlockRecord == [
    slot: Nat,
    parent: Nat,
    hash: Nat,
    proposer: Validators
]

VoteRecord == [
    kind: VoteKind,
    round: 0..2,
    block: Nat \cup {NULL}
]

CertificateRecord == [
    status: CertificateStatus,
    slot: Nat,
    block: Nat \cup {NULL},
    signers: SUBSET Validators
]

RotorRecord == [
    received: Nat \cup {NULL} \* Number of shards accumulated (NULL -> no block)
]

AppendSeq(seq, elem) == seq \o <<elem>>

Modulo(a, b) == IF b = 0 THEN 0 ELSE a - b * (a \div b)

Leader(slot) == 1 + Modulo(slot - 1, ValidatorCount)

SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

PushWindow(window, slot) ==
    IF Len(window) = 0 THEN <<slot>>
    ELSE IF slot \in SeqToSet(window) THEN window
         ELSE IF Len(window) < WindowSize THEN AppendSeq(window, slot)
         ELSE AppendSeq(Tail(window), slot)

RECURSIVE RemoveSlotRec(_,_)
RemoveSlotRec(window, slot) ==
    IF window = <<>> THEN <<>>
    ELSE IF Head(window) = slot THEN Tail(window)
    ELSE <<Head(window)>> \o RemoveSlotRec(Tail(window), slot)

RemoveSlot(window, slot) == RemoveSlotRec(window, slot)

====
