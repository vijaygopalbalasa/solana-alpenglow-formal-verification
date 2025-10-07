---------------------------- MODULE MC_Full_10val_fast ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

M == INSTANCE AlpenglowFull WITH
  Validators <- 1..10,
  Stake <- [i \in 1..10 |-> 10],
  MaxSlot <- 1,
  FastThreshold <- 80,
  SlowThreshold <- 60,
  ByzantineThreshold <- 20,
  MessageDelay <- 1,
  BlockTimeout <- 1,
  FastTimeout <- 2,
  SlowTimeout <- 4

Spec == M!Spec

TypeInvariant == M!TypeInvariant
NoConflictingFinalization == M!NoConflictingFinalization
ChainConsistency == M!ChainConsistency
OneCertificatePerSlot == M!OneCertificatePerSlot
NoEquivocation == M!NoEquivocation

=============================================================================
