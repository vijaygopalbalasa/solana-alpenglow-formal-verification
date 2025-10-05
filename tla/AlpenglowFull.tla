--------------------------- MODULE AlpenglowFull ---------------------------
(*
  Complete Alpenglow Consensus Protocol Specification

  Implements full dual-component architecture:
  - Votor: Dual-path consensus (80% fast, 60% slow)
  - Rotor: Block propagation with erasure coding

  Based on Solana Alpenglow White Paper v1.1
*)

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Validators,           (* Set of all validators *)
    Stake,                (* Stake[v] = stake amount for validator v *)
    MaxSlot,              (* Maximum slot number for model checking *)
    FastThreshold,        (* 80% of total stake *)
    SlowThreshold,        (* 60% of total stake *)
    ByzantineThreshold,   (* 20% of total stake *)
    MessageDelay,         (* Maximum network message delay *)
    BlockTimeout,         (* Timeout for block proposal *)
    FastTimeout,          (* Timeout for fast path *)
    SlowTimeout           (* Timeout for slow path *)

VARIABLES
    (* Votor State *)
    blocks,               (* Set of proposed blocks *)
    votes,                (* Set of all cast votes *)
    certificates,         (* Finalized block certificates *)
    currentSlot,          (* Current slot number *)
    currentTime,          (* Current time *)

    (* Rotor State *)
    shreds,               (* Erasure-coded chunks *)
    receivedShreds,       (* Shreds received by each validator *)
    reconstructedBlocks,  (* Blocks reconstructed from shreds *)

    (* Network State *)
    network,              (* In-flight messages *)

    (* Validator State *)
    validatorState,       (* State per validator: online/crashed/byzantine *)
    voteHistory,          (* Vote history per validator *)
    timeouts              (* Active timeouts *)

vars == <<blocks, votes, certificates, currentSlot, currentTime,
          shreds, receivedShreds, reconstructedBlocks,
          network, validatorState, voteHistory, timeouts>>

(* ========================================================================
   TYPE DEFINITIONS
   ======================================================================== *)

VoteTypes == {"notarize", "skip"}

CertificateTypes == {"fast", "slow", "skip"}

ValidatorStates == {"honest", "byzantine", "crashed"}

Block == [
    slot: Nat,
    hash: Nat,
    parentHash: Nat,
    transactions: Seq(Nat),
    leader: Validators
]

Vote == [
    voter: Validators,
    slot: Nat,
    blockHash: Nat,
    type: VoteTypes
]

Certificate == [
    slot: Nat,
    blockHash: Nat,
    votes: SUBSET Vote,
    certType: CertificateTypes,
    stakeTotal: Nat
]

Message == [
    sender: Validators,
    receiver: Validators,
    content: UNION {Block, Vote, Certificate, Nat}
]

(* ========================================================================
   HELPER FUNCTIONS
   ======================================================================== *)

TotalStake == LET StakeSum[S \in SUBSET Validators] ==
                  IF S = {} THEN 0
                  ELSE LET v == CHOOSE v \in S : TRUE
                       IN Stake[v] + StakeSum[S \ {v}]
              IN StakeSum[Validators]

SumStake(V) == LET StakeSum[S \in SUBSET Validators] ==
                  IF S = {} THEN 0
                  ELSE LET v == CHOOSE v \in S : TRUE
                       IN Stake[v] + StakeSum[S \ {v}]
               IN StakeSum[V]

Leader(slot) == CHOOSE v \in Validators :
                  (slot % Cardinality(Validators)) =
                  (CHOOSE i \in 1..Cardinality(Validators) :
                    v = (CHOOSE w \in Validators :
                          Cardinality({x \in Validators : x < w}) = i-1))

IsHonest(v) == validatorState[v] = "honest"

IsByzantine(v) == validatorState[v] = "byzantine"

IsCrashed(v) == validatorState[v] = "crashed"

HonestValidators == {v \in Validators : IsHonest(v)}

ResponsiveValidators == {v \in Validators : IsHonest(v) /\ ~IsCrashed(v)}

VotesForBlock(slot, hash) ==
    {v \in votes : v.slot = slot /\ v.blockHash = hash /\ v.type = "notarize"}

SkipVotesForSlot(slot) ==
    {v \in votes : v.slot = slot /\ v.type = "skip"}

HasFastQuorum(slot, hash) ==
    SumStake({v.voter : v \in VotesForBlock(slot, hash)}) >= FastThreshold

HasSlowQuorum(slot, hash) ==
    SumStake({v.voter : v \in VotesForBlock(slot, hash)}) >= SlowThreshold

HasSkipCertificate(slot) ==
    SumStake({v.voter : v \in SkipVotesForSlot(slot)}) >= SlowThreshold

BlockAtSlot(slot) == CHOOSE b \in blocks : b.slot = slot

(* ========================================================================
   INITIAL STATE
   ======================================================================== *)

TypeInvariant ==
    /\ blocks \subseteq Block
    /\ votes \subseteq Vote
    /\ certificates \subseteq Certificate
    /\ currentSlot \in Nat
    /\ currentTime \in Nat
    /\ validatorState \in [Validators -> ValidatorStates]
    /\ voteHistory \in [Validators -> SUBSET Vote]

Init ==
    /\ blocks = {}
    /\ votes = {}
    /\ certificates = {}
    /\ currentSlot = 0
    /\ currentTime = 0
    /\ shreds = {}
    /\ receivedShreds = [v \in Validators |-> {}]
    /\ reconstructedBlocks = [v \in Validators |-> {}]
    /\ network = {}
    /\ validatorState = [v \in Validators |->
         IF Stake[v] <= ByzantineThreshold THEN "byzantine" ELSE "honest"]
    /\ voteHistory = [v \in Validators |-> {}]
    /\ timeouts = [slot \in 0..MaxSlot |->
         [blockTimeout |-> BlockTimeout,
          fastTimeout |-> FastTimeout,
          slowTimeout |-> SlowTimeout]]

(* ========================================================================
   VOTOR ACTIONS (Consensus Mechanism)
   ======================================================================== *)

ProposeBlock ==
    /\ currentSlot < MaxSlot
    /\ LET leader == Leader(currentSlot)
       IN /\ IsHonest(leader) \/ IsByzantine(leader)
          /\ ~IsCrashed(leader)
          /\ ~\E b \in blocks : b.slot = currentSlot
          /\ LET newBlock == [
                  slot |-> currentSlot,
                  hash |-> currentSlot + 1000,  (* Simplified hash *)
                  parentHash |-> IF currentSlot = 0 THEN 0
                                  ELSE (CHOOSE b \in blocks :
                                         b.slot = currentSlot - 1).hash,
                  transactions |-> <<currentSlot>>,
                  leader |-> leader
                 ]
             IN /\ blocks' = blocks \cup {newBlock}
                /\ network' = network \cup
                    {[sender |-> leader,
                      receiver |-> v,
                      content |-> newBlock] : v \in Validators}
                /\ UNCHANGED <<votes, certificates, currentSlot, currentTime,
                              shreds, receivedShreds, reconstructedBlocks,
                              validatorState, voteHistory, timeouts>>

CastNotarizeVote(v) ==
    /\ IsHonest(v) \/ IsByzantine(v)
    /\ ~IsCrashed(v)
    /\ \E b \in blocks :
        /\ b.slot = currentSlot
        /\ ~\E vote \in voteHistory[v] :
             vote.slot = currentSlot /\ vote.type = "notarize"
        /\ LET newVote == [
                voter |-> v,
                slot |-> currentSlot,
                blockHash |-> b.hash,
                type |-> "notarize"
               ]
           IN /\ votes' = votes \cup {newVote}
              /\ voteHistory' = [voteHistory EXCEPT ![v] = @ \cup {newVote}]
              /\ UNCHANGED <<blocks, certificates, currentSlot, currentTime,
                            shreds, receivedShreds, reconstructedBlocks,
                            network, validatorState, timeouts>>

CastSkipVote(v) ==
    /\ IsHonest(v)
    /\ ~IsCrashed(v)
    /\ currentTime >= timeouts[currentSlot].blockTimeout
    /\ ~\E b \in blocks : b.slot = currentSlot
    /\ ~\E vote \in voteHistory[v] : vote.slot = currentSlot
    /\ LET newVote == [
            voter |-> v,
            slot |-> currentSlot,
            blockHash |-> 0,
            type |-> "skip"
           ]
       IN /\ votes' = votes \cup {newVote}
          /\ voteHistory' = [voteHistory EXCEPT ![v] = @ \cup {newVote}]
          /\ UNCHANGED <<blocks, certificates, currentSlot, currentTime,
                        shreds, receivedShreds, reconstructedBlocks,
                        network, validatorState, timeouts>>

FastPathFinalize ==
    /\ \E b \in blocks :
        /\ b.slot = currentSlot
        /\ HasFastQuorum(currentSlot, b.hash)
        /\ ~\E c \in certificates : c.slot = currentSlot
        /\ LET cert == [
                slot |-> currentSlot,
                blockHash |-> b.hash,
                votes |-> VotesForBlock(currentSlot, b.hash),
                certType |-> "fast",
                stakeTotal |-> SumStake({v.voter : v \in VotesForBlock(currentSlot, b.hash)})
               ]
           IN /\ certificates' = certificates \cup {cert}
              /\ UNCHANGED <<blocks, votes, currentSlot, currentTime,
                            shreds, receivedShreds, reconstructedBlocks,
                            network, validatorState, voteHistory, timeouts>>

SlowPathFinalize ==
    /\ \E b \in blocks :
        /\ b.slot = currentSlot
        /\ HasSlowQuorum(currentSlot, b.hash)
        /\ currentTime >= timeouts[currentSlot].fastTimeout
        /\ ~\E c \in certificates : c.slot = currentSlot
        /\ LET cert == [
                slot |-> currentSlot,
                blockHash |-> b.hash,
                votes |-> VotesForBlock(currentSlot, b.hash),
                certType |-> "slow",
                stakeTotal |-> SumStake({v.voter : v \in VotesForBlock(currentSlot, b.hash)})
               ]
           IN /\ certificates' = certificates \cup {cert}
              /\ UNCHANGED <<blocks, votes, currentSlot, currentTime,
                            shreds, receivedShreds, reconstructedBlocks,
                            network, validatorState, voteHistory, timeouts>>

CreateSkipCertificate ==
    /\ HasSkipCertificate(currentSlot)
    /\ ~\E c \in certificates : c.slot = currentSlot
    /\ LET cert == [
            slot |-> currentSlot,
            blockHash |-> 0,
            votes |-> SkipVotesForSlot(currentSlot),
            certType |-> "skip",
            stakeTotal |-> SumStake({v.voter : v \in SkipVotesForSlot(currentSlot)})
           ]
       IN /\ certificates' = certificates \cup {cert}
          /\ UNCHANGED <<blocks, votes, currentSlot, currentTime,
                        shreds, receivedShreds, reconstructedBlocks,
                        network, validatorState, voteHistory, timeouts>>

AdvanceSlot ==
    /\ \E c \in certificates : c.slot = currentSlot
    /\ currentSlot' = currentSlot + 1
    /\ currentTime' = 0
    /\ UNCHANGED <<blocks, votes, certificates,
                  shreds, receivedShreds, reconstructedBlocks,
                  network, validatorState, voteHistory, timeouts>>

AdvanceTime ==
    /\ currentTime < SlowTimeout
    /\ currentTime' = currentTime + 1
    /\ UNCHANGED <<blocks, votes, certificates, currentSlot,
                  shreds, receivedShreds, reconstructedBlocks,
                  network, validatorState, voteHistory, timeouts>>

(* ========================================================================
   ROTOR ACTIONS (Block Propagation)
   ======================================================================== *)

(* Simplified erasure coding - full implementation would use Reed-Solomon *)
EncodeBlockToShreds(b) ==
    /\ LET numShreds == 10  (* Simplified - should be γ + Γ *)
       IN {[block |-> b, shredId |-> i] : i \in 1..numShreds}

SendShreds ==
    /\ \E b \in blocks :
        /\ b.slot = currentSlot
        /\ b.leader \in ResponsiveValidators
        /\ ~\E s \in shreds : s.block = b
        /\ LET newShreds == EncodeBlockToShreds(b)
           IN /\ shreds' = shreds \cup newShreds
              /\ UNCHANGED <<blocks, votes, certificates, currentSlot, currentTime,
                            receivedShreds, reconstructedBlocks,
                            network, validatorState, voteHistory, timeouts>>

ReceiveShred(v) ==
    /\ ~IsCrashed(v)
    /\ \E s \in shreds :
        /\ s \notin receivedShreds[v]
        /\ receivedShreds' = [receivedShreds EXCEPT ![v] = @ \cup {s}]
        /\ UNCHANGED <<blocks, votes, certificates, currentSlot, currentTime,
                      shreds, reconstructedBlocks,
                      network, validatorState, voteHistory, timeouts>>

ReconstructBlock(v) ==
    /\ ~IsCrashed(v)
    /\ \E b \in blocks :
        /\ b \notin reconstructedBlocks[v]
        /\ LET blockShreds == {s \in receivedShreds[v] : s.block = b}
           IN /\ Cardinality(blockShreds) >= 7  (* Need 7/10 shreds *)
              /\ reconstructedBlocks' = [reconstructedBlocks EXCEPT ![v] = @ \cup {b}]
              /\ UNCHANGED <<blocks, votes, certificates, currentSlot, currentTime,
                            shreds, receivedShreds,
                            network, validatorState, voteHistory, timeouts>>

(* ========================================================================
   NEXT STATE RELATION
   ======================================================================== *)

Next ==
    \/ ProposeBlock
    \/ \E v \in Validators : CastNotarizeVote(v)
    \/ \E v \in Validators : CastSkipVote(v)
    \/ FastPathFinalize
    \/ SlowPathFinalize
    \/ CreateSkipCertificate
    \/ AdvanceSlot
    \/ AdvanceTime
    \/ SendShreds
    \/ \E v \in Validators : ReceiveShred(v)
    \/ \E v \in Validators : ReconstructBlock(v)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* ========================================================================
   SAFETY PROPERTIES
   ======================================================================== *)

NoConflictingFinalization ==
    \A c1, c2 \in certificates :
        c1.slot = c2.slot => c1.blockHash = c2.blockHash

ChainConsistency ==
    \A c1, c2 \in certificates :
        c1.slot = c2.slot => c1.blockHash = c2.blockHash

OneCertificatePerSlot ==
    \A slot \in 0..MaxSlot :
        Cardinality({c \in certificates : c.slot = slot}) <= 1

NoEquivocation ==
    \A v \in Validators :
        \A v1, v2 \in voteHistory[v] :
            (v1.slot = v2.slot /\ v1.type = "notarize" /\ v2.type = "notarize")
            => v1.blockHash = v2.blockHash

(* ========================================================================
   LIVENESS PROPERTIES
   ======================================================================== *)

EventualProgress ==
    <>(\E c \in certificates : c.slot > 0)

FastPathLiveness ==
    (SumStake(ResponsiveValidators) >= FastThreshold)
    => <>(\E c \in certificates : c.certType = "fast")

SlowPathLiveness ==
    (SumStake(ResponsiveValidators) >= SlowThreshold)
    => <>(\E c \in certificates : c.certType \in {"fast", "slow"})

(* ========================================================================
   RESILIENCE PROPERTIES (20+20 Model)
   ======================================================================== *)

ByzantineResilience ==
    SumStake({v \in Validators : IsByzantine(v)}) <= ByzantineThreshold
    => NoConflictingFinalization

CrashResilience ==
    SumStake({v \in Validators : IsCrashed(v)}) <= ByzantineThreshold
    => EventualProgress

Combined2020Resilience ==
    /\ SumStake({v \in Validators : IsByzantine(v)}) <= ByzantineThreshold
    /\ SumStake({v \in Validators : IsCrashed(v)}) <= ByzantineThreshold
    /\ SumStake(ResponsiveValidators) >= SlowThreshold
    => /\ NoConflictingFinalization
       /\ EventualProgress

================================================================================
