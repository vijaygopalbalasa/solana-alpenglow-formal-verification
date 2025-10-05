---- MODULE AlpenglowProtocol ----
EXTENDS AlpenglowCore, TLC

VARIABLES
    currentSlot,
    slotWindow,         \* sequence of currently open slots (bounded by WindowSize)
    slotTimers,         \* slot -> ticks since opening
    blockPool,          \* slot -> set of candidate blocks
    chain,              \* sequence of finalized blocks
    votes,              \* validator -> slot -> vote record
    certificates,       \* slot -> certificate record
    validatorState,     \* validator -> status
    rotorSource,        \* slot -> block hash currently disseminated
    rotorRecipients,    \* slot -> validators that relayed the shard
    timeouts,           \* slot -> BOOLEAN (slow-path timeout triggered)
    nextHash            \* monotonic counter for fresh block hashes

vars == <<currentSlot, slotWindow, slotTimers, blockPool, chain, votes, certificates,
          validatorState, rotorSource, rotorRecipients, timeouts, nextHash>>

(*************************************************************************)
(* Helper operators                                                        *)
(*************************************************************************)

Slots == 1..MaxSlot

BlockHashes(slot) == {b.hash : b \in blockPool[slot]}

ActiveSlots == SeqToSet(slotWindow)

OldestSlot == IF Len(slotWindow) = 0 THEN 0 ELSE Head(slotWindow)

RotorStake(slot) == SumStake(rotorRecipients[slot])

Reconstructable(slot) ==
    rotorSource[slot] # NULL
    /\ Cardinality(rotorRecipients[slot]) >= K
    /\ HasStake(rotorRecipients[slot], FastThreshold)

VoteFor(v, slot) == votes[v][slot].block

VoteKindOf(v, slot) == votes[v][slot].kind

HonestValidators == {v \in Validators : validatorState[v] = "online"}
ByzantineValidators == {v \in Validators : validatorState[v] = "byzantine"}
OfflineValidators == {v \in Validators : validatorState[v] = "offline"}

FastSigners(slot, blockHash) ==
    {v \in Validators :
        VoteKindOf(v, slot) \in {"fast", "final"} /\ VoteFor(v, slot) = blockHash}

SlowSigners(slot, blockHash) ==
    {v \in Validators :
        VoteKindOf(v, slot) \in {"fast", "fallback", "final"} /\ VoteFor(v, slot) = blockHash}

FinalSigners(slot, blockHash) ==
    {v \in Validators :
        VoteKindOf(v, slot) = "final" /\ VoteFor(v, slot) = blockHash}

SkipSigners(slot) ==
    {v \in Validators : VoteKindOf(v, slot) = "skip"}

BlockForHash(slot, hash) ==
    CHOOSE b \in blockPool[slot] : b.hash = hash

CertificateReady(slot) ==
    certificates[slot].status \in {"fast", "final", "skip"}

NoPendingBlock(slot) == blockPool[slot] = {}

HonestFastNoDouble ==
    \A slot \in Slots :
        \A b1 \in BlockHashes(slot) : \A b2 \in BlockHashes(slot) :
            b1 # b2 =>
                (FastSigners(slot, b1) \cap FastSigners(slot, b2) \cap HonestValidators) = {}

HonestSlowNoDouble ==
    \A slot \in Slots :
        \A b1 \in BlockHashes(slot) : \A b2 \in BlockHashes(slot) :
            b1 # b2 =>
                (SlowSigners(slot, b1) \cap SlowSigners(slot, b2) \cap HonestValidators) = {}

HonestFinalNoDouble ==
    \A slot \in Slots :
        \A b1 \in BlockHashes(slot) : \A b2 \in BlockHashes(slot) :
            b1 # b2 =>
                (FinalSigners(slot, b1) \cap FinalSigners(slot, b2) \cap HonestValidators) = {}

(*************************************************************************)
(* Initial state                                                            *)
(*************************************************************************)

GenesisBlock == [slot |-> 0, parent |-> 0, hash |-> 0, proposer |-> Leader(1)]

Init ==
    /\ currentSlot = 1
    /\ slotWindow = <<1>>
    /\ slotTimers = [s \in Slots |-> 0]
    /\ blockPool = [s \in Slots |-> {}]
    /\ chain = <<GenesisBlock>>
    /\ votes = [v \in Validators |-> [s \in Slots |-> [
            kind |-> "none",
            round |-> 0,
            block |-> NULL
        ]]]
    /\ certificates = [s \in Slots |-> [
            status |-> "none",
            slot |-> s,
            block |-> NULL,
            signers |-> {}
        ]]
    /\ validatorState = [v \in Validators |-> "online"]
    /\ rotorSource = [s \in Slots |-> NULL]
    /\ rotorRecipients = [s \in Slots |-> {}]
    /\ timeouts = [s \in Slots |-> FALSE]
    /\ nextHash = 1

(*************************************************************************)
(* Protocol actions                                                         *)
(*************************************************************************)

LeaderPropose ==
    \E leader \in Validators :
    \E slot \in ActiveSlots :
        /\ leader = Leader(slot)
        /\ validatorState[leader] = "online"
        /\ certificates[slot].status = "none"
        /\ ~\E b \in blockPool[slot] : b.proposer = leader
        /\ LET parentHash == chain[Len(chain)].hash
               newBlock == [
                   slot |-> slot,
                   parent |-> parentHash,
                   hash |-> nextHash,
                   proposer |-> leader
               ]
           IN /\ blockPool' = [blockPool EXCEPT ![slot] = blockPool[slot] \cup {newBlock}]
              /\ nextHash' = nextHash + 1
              /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, chain, votes, certificates,
                             validatorState, rotorSource, rotorRecipients, timeouts>>

AdversarialPropose ==
    \E attacker \in Validators :
    \E slot \in ActiveSlots :
        /\ validatorState[attacker] = "byzantine"
        /\ certificates[slot].status = "none"
        /\ LET parentHash == chain[Len(chain)].hash
               newBlock == [
                   slot |-> slot,
                   parent |-> parentHash,
                   hash |-> nextHash,
                   proposer |-> attacker
               ]
           IN /\ blockPool[slot] \in SUBSET BlockRecord
              /\ blockPool' = [blockPool EXCEPT ![slot] = blockPool[slot] \cup {newBlock}]
              /\ nextHash' = nextHash + 1
              /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, chain, votes, certificates,
                             validatorState, rotorSource, rotorRecipients, timeouts>>

RotorDeliver ==
    \E validator \in Validators : \E slot \in ActiveSlots :
        /\ validatorState[validator] = "online"
        /\ blockPool[slot] # {}
        /\ validator \notin rotorRecipients[slot]
        /\ Cardinality(rotorRecipients[slot]) < K
        /\ LET chosenBlock == CHOOSE b \in blockPool[slot] : TRUE
               source == rotorSource[slot]
           IN /\ (source = NULL \/ source = chosenBlock.hash)
              /\ rotorSource' = [rotorSource EXCEPT ![slot] =
                        IF source = NULL THEN chosenBlock.hash ELSE source]
              /\ rotorRecipients' = [rotorRecipients EXCEPT ![slot] = rotorRecipients[slot] \cup {validator}]
              /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, chain, votes,
                             certificates, validatorState, timeouts, nextHash>>

Tick ==
    LET updatedTimers == [s \in Slots |-> IF s \in ActiveSlots THEN slotTimers[s] + 1 ELSE slotTimers[s]]
        updatedTimeouts == [s \in Slots |->
            IF s \in ActiveSlots THEN (timeouts[s] \/ updatedTimers[s] >= TimeoutLimit)
            ELSE timeouts[s]]
    IN /\ slotTimers' = updatedTimers
       /\ timeouts' = updatedTimeouts
       /\ UNCHANGED <<currentSlot, slotWindow, blockPool, chain, votes, certificates,
                      validatorState, rotorSource, rotorRecipients, nextHash>>

CastFastVote ==
    \E v \in Validators : \E slot \in ActiveSlots : \E hash \in BlockHashes(slot) :
        /\ validatorState[v] = "online"
        /\ votes[v][slot].kind = "none"
        /\ Reconstructable(slot)
        /\ rotorSource[slot] = hash
        /\ votes' = [votes EXCEPT ![v][slot] = [
                kind |-> "fast",
                round |-> 1,
                block |-> hash
            ]]
        /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, chain, certificates,
                       validatorState, rotorSource, rotorRecipients, timeouts, nextHash>>

CastFallbackVote ==
    \E v \in Validators : \E slot \in ActiveSlots : \E hash \in BlockHashes(slot) :
        /\ validatorState[v] = "online"
        /\ timeouts[slot]
        /\ votes[v][slot].kind \in {"none", "fast"}
        /\ rotorSource[slot] = hash
        /\ votes' = [votes EXCEPT ![v][slot] = [
                kind |-> "fallback",
                round |-> 1,
                block |-> hash
            ]]
        /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, chain, certificates,
                       validatorState, rotorSource, rotorRecipients, timeouts, nextHash>>

CastFinalVote ==
    \E v \in Validators : \E slot \in ActiveSlots : \E hash \in BlockHashes(slot) :
        /\ validatorState[v] = "online"
        /\ certificates[slot].status = "slow"
        /\ votes[v][slot].kind \in {"fast", "fallback"}
        /\ certificates[slot].block = hash
        /\ votes' = [votes EXCEPT ![v][slot] = [
                kind |-> "final",
                round |-> 2,
                block |-> hash
            ]]
        /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, chain, certificates,
                       validatorState, rotorSource, rotorRecipients, timeouts, nextHash>>

CastSkipVote ==
    \E v \in Validators : \E slot \in ActiveSlots :
        /\ validatorState[v] = "online"
        /\ blockPool[slot] = {}
        /\ votes[v][slot].kind = "none"
        /\ votes' = [votes EXCEPT ![v][slot] = [
                kind |-> "skip",
                round |-> 1,
                block |-> NULL
            ]]
        /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, chain, certificates,
                       validatorState, rotorSource, rotorRecipients, timeouts, nextHash>>

ByzantineVote ==
    \E v \in Validators : \E slot \in ActiveSlots : \E kind \in VoteKind :
        \E hash \in (BlockHashes(slot) \cup {NULL}) :
        /\ validatorState[v] = "byzantine"
        /\ votes' = [votes EXCEPT ![v][slot] = [
                kind |-> kind,
                round |-> IF kind = "final" THEN 2 ELSE IF kind = "none" THEN 0 ELSE 1,
                block |-> hash
            ]]
        /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, chain, certificates,
                       validatorState, rotorSource, rotorRecipients, timeouts, nextHash>>

FormFastCertificate ==
    \E slot \in ActiveSlots : \E hash \in BlockHashes(slot) :
        LET signers == FastSigners(slot, hash) IN
        /\ certificates[slot].status = "none"
        /\ HasStake(signers, FastThreshold)
        /\ certificates' = [certificates EXCEPT ![slot] = [
                status |-> "fast",
                slot |-> slot,
                block |-> hash,
                signers |-> signers
            ]]
        /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, chain, votes, validatorState,
                       rotorSource, rotorRecipients, timeouts, nextHash>>

FormSlowCertificate ==
    \E slot \in ActiveSlots : \E hash \in BlockHashes(slot) :
        LET signers == SlowSigners(slot, hash) IN
        /\ certificates[slot].status = "none"
        /\ timeouts[slot]
        /\ HasStake(signers, SlowThreshold)
        /\ ~HasStake(signers, FastThreshold)
        /\ certificates' = [certificates EXCEPT ![slot] = [
                status |-> "slow",
                slot |-> slot,
                block |-> hash,
                signers |-> signers
            ]]
        /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, chain, votes, validatorState,
                       rotorSource, rotorRecipients, timeouts, nextHash>>

UpgradeToFinalCertificate ==
    \E slot \in ActiveSlots : \E hash \in BlockHashes(slot) :
        LET signers == FinalSigners(slot, hash) IN
        /\ certificates[slot].status = "slow"
        /\ certificates[slot].block = hash
        /\ HasStake(signers, SlowThreshold)
        /\ certificates' = [certificates EXCEPT ![slot] = [
                status |-> "final",
                slot |-> slot,
                block |-> hash,
                signers |-> signers
            ]]
        /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, chain, votes, validatorState,
                       rotorSource, rotorRecipients, timeouts, nextHash>>

FormSkipCertificate ==
    \E slot \in ActiveSlots :
        LET signers == SkipSigners(slot) IN
        /\ certificates[slot].status = "none"
        /\ HasStake(signers, SlowThreshold)
        /\ blockPool[slot] = {}
        /\ certificates' = [certificates EXCEPT ![slot] = [
                status |-> "skip",
                slot |-> slot,
                block |-> NULL,
                signers |-> signers
            ]]
        /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, chain, votes, validatorState,
                       rotorSource, rotorRecipients, timeouts, nextHash>>

RecordFinalization ==
    \E slot \in ActiveSlots :
        /\ slot <= currentSlot
        /\ certificates[slot].status \in {"fast", "final"}
        /\ \E hash \in BlockHashes(slot) : hash = certificates[slot].block
        /\ ~\E i \in DOMAIN chain : chain[i].slot = slot
        /\ LET finalBlock == BlockForHash(slot, certificates[slot].block)
           IN /\ chain' = AppendSeq(chain, finalBlock)
              /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, votes, certificates,
                             validatorState, rotorSource, rotorRecipients, timeouts, nextHash>>

RetireSlot ==
    \E slot \in ActiveSlots :
        LET initVote == [kind |-> "none", round |-> 0, block |-> NULL]
        IN /\ CertificateReady(slot)
           /\ slotWindow # <<>>
           /\ slotWindow' = RemoveSlot(slotWindow, slot)
           /\ slotTimers' = [slotTimers EXCEPT ![slot] = 0]
           /\ timeouts' = [timeouts EXCEPT ![slot] = FALSE]
           /\ blockPool' = [blockPool EXCEPT ![slot] = {}]
           /\ votes' = [v \in Validators |-> [s \in Slots |-> IF s = slot THEN initVote ELSE votes[v][s]]]
           /\ rotorSource' = [rotorSource EXCEPT ![slot] = NULL]
           /\ rotorRecipients' = [rotorRecipients EXCEPT ![slot] = {}]
           /\ UNCHANGED <<currentSlot, chain, certificates, validatorState, nextHash>>

OpenNextSlot ==
    LET newSlot == currentSlot + 1
    IN /\ currentSlot < MaxSlot
       /\ Len(slotWindow) < WindowSize
       /\ currentSlot' = newSlot
       /\ slotWindow' = PushWindow(slotWindow, newSlot)
       /\ slotTimers' = [slotTimers EXCEPT ![newSlot] = 0]
       /\ blockPool' = [blockPool EXCEPT ![newSlot] = {}]
       /\ LET initVote == [kind |-> "none", round |-> 0, block |-> NULL]
          IN votes' = [v \in Validators |-> [s \in Slots |-> IF s = newSlot THEN initVote ELSE votes[v][s]]]
       /\ certificates' = [certificates EXCEPT ![newSlot] = [
                status |-> "none",
                slot |-> newSlot,
                block |-> NULL,
                signers |-> {}
            ]]
       /\ rotorSource' = [rotorSource EXCEPT ![newSlot] = NULL]
       /\ rotorRecipients' = [rotorRecipients EXCEPT ![newSlot] = {}]
       /\ timeouts' = [timeouts EXCEPT ![newSlot] = FALSE]
       /\ nextHash' = nextHash
       /\ UNCHANGED <<chain, validatorState>>

BecomeByzantine ==
    \E v \in Validators :
        LET futureState == [validatorState EXCEPT ![v] = "byzantine"]
            byzStake == SumStake({u \in Validators : futureState[u] = "byzantine"})
        IN /\ validatorState[v] # "byzantine"
           /\ byzStake <= ByzantineThreshold
           /\ validatorState' = futureState
           /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, chain, votes, certificates,
                         rotorSource, rotorRecipients, timeouts, nextHash>>

GoOffline ==
    \E v \in Validators :
        /\ validatorState[v] = "online"
        /\ validatorState' = [validatorState EXCEPT ![v] = "offline"]
        /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, chain, votes, certificates,
                       rotorSource, rotorRecipients, timeouts, nextHash>>

RecoverValidator ==
    \E v \in Validators :
        /\ validatorState[v] # "online"
        /\ validatorState' = [validatorState EXCEPT ![v] = "online"]
        /\ UNCHANGED <<currentSlot, slotWindow, slotTimers, blockPool, chain, votes, certificates,
                       rotorSource, rotorRecipients, timeouts, nextHash>>

Next ==
    LeaderPropose
    \/ AdversarialPropose
    \/ RotorDeliver
    \/ Tick
    \/ CastFastVote
    \/ CastFallbackVote
    \/ CastFinalVote
    \/ CastSkipVote
    \/ ByzantineVote
    \/ FormFastCertificate
    \/ FormSlowCertificate
    \/ UpgradeToFinalCertificate
    \/ FormSkipCertificate
    \/ RecordFinalization
    \/ RetireSlot
    \/ OpenNextSlot
    \/ BecomeByzantine
    \/ GoOffline
    \/ RecoverValidator

Spec == Init /\ [][Next]_vars

(*************************************************************************)
(* Safety properties                                                        *)
(*************************************************************************)

TypeInvariant ==
    /\ currentSlot \in Slots
    /\ slotWindow \in Seq(Slots)
    /\ Len(slotWindow) <= WindowSize
    /\ SeqToSet(slotWindow) \subseteq Slots
    /\ slotTimers \in [Slots -> Nat]
    /\ blockPool \in [Slots -> SUBSET BlockRecord]
    /\ chain \in Seq(BlockRecord)
    /\ votes \in [Validators -> [Slots -> VoteRecord]]
    /\ certificates \in [Slots -> CertificateRecord]
    /\ validatorState \in [Validators -> ValidatorStatus]
    /\ rotorSource \in [Slots -> (Nat \cup {NULL})]
    /\ rotorRecipients \in [Slots -> SUBSET Validators]
    /\ timeouts \in [Slots -> BOOLEAN]
    /\ nextHash \in Nat

NoConflictingFinalization ==
    \A slot \in Slots :
        LET cert == certificates[slot] IN
        cert.status \in {"fast", "final"} =>
            /\ cert.block # NULL
            /\ \A b1, b2 \in BlockHashes(slot) :
                (b1 # b2) => ~(HasStake(FastSigners(slot, b1), FastThreshold)
                              /\ HasStake(FastSigners(slot, b2), FastThreshold))
            /\ \A b1, b2 \in BlockHashes(slot) :
                (b1 # b2) => ~(HasStake(FinalSigners(slot, b1), SlowThreshold)
                              /\ HasStake(FinalSigners(slot, b2), SlowThreshold))

CertificateStakeValid ==
    \A slot \in Slots :
        LET cert == certificates[slot] IN
        CASE cert.status = "fast" -> HasStake(cert.signers, FastThreshold)
        [] cert.status = "slow" -> HasStake(cert.signers, SlowThreshold)
        [] cert.status = "final" -> HasStake(cert.signers, SlowThreshold)
        [] cert.status = "skip" -> HasStake(cert.signers, SlowThreshold)
        [] OTHER -> TRUE

ByzantineStakeBound ==
    SumStake(ByzantineValidators) <= ByzantineThreshold

RotorConsistency ==
    \A slot \in Slots :
        rotorSource[slot] # NULL => rotorSource[slot] \in BlockHashes(slot)

ChainConsistency ==
    \A i, j \in DOMAIN chain :
        (i # j /\ chain[i].slot = chain[j].slot) => chain[i] = chain[j]

OneFinalizedBlockPerSlot ==
    \A slot \in Slots :
        Cardinality({b \in DOMAIN chain : chain[b].slot = slot}) <= 1

SafetyInvariant ==
    TypeInvariant
    /\ NoConflictingFinalization
    /\ CertificateStakeValid
    /\ ByzantineStakeBound
    /\ RotorConsistency
    /\ ChainConsistency
    /\ OneFinalizedBlockPerSlot
    /\ HonestFastNoDouble
    /\ HonestSlowNoDouble
    /\ HonestFinalNoDouble

\* SafetyInvariant is discharged by the TLC configs under configs/ and supported by
\* the TLAPS lemmas in proofs/. We do not restate it as a theorem here to avoid
\* duplicating the model-checking obligations.

==== 
