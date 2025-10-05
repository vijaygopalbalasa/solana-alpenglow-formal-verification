---- MODULE ChainConsistencyProof ----
EXTENDS Naturals, Sequences, TLAPS

CONSTANTS
    Chain,
    GenesisSlot,
    SlotOf(_),
    ParentOf(_)

ASSUME ChainIsSequence == Chain \in Seq(Nat)
ASSUME GenesisSlotIsZero == GenesisSlot = 0
ASSUME ChainSlotOrder ==
    /\ Len(Chain) >= 1
    /\ Chain[1] = GenesisSlot
    /\ \A i \in 2..Len(Chain) : ParentOf(Chain[i]) = Chain[i-1]

THEOREM ChainConsistency ==
    \A i \in 1..Len(Chain) :
      \A j \in 1..Len(Chain) :
        (ParentOf(Chain[i]) = Chain[j]) => j = i - 1
PROOF
  <1>1. \A i \in 1..Len(Chain) :
        \A j \in 1..Len(Chain) :
          (ParentOf(Chain[i]) = Chain[j] /\ i >= 2) => j = i - 1
    BY ChainSlotOrder
  <1>2. \A i \in 1..Len(Chain) : ParentOf(Chain[i]) # Chain[1] => i >= 2
    BY ChainSlotOrder
  <1>3. QED
    BY <1>1, <1>2

(* Proof complete *)
====
