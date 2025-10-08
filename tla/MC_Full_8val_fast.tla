---------------------------- MODULE MC_Full_8val_fast ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Mirror AlpenglowFull variables so TLC treats them as the root module's VARIABLES
VARIABLES 
  blocks, votes, certificates, currentSlot, currentTime,
  shreds, receivedShreds, reconstructedBlocks,
  network, validatorState, voteHistory, timeouts

M == INSTANCE AlpenglowFull WITH
  Validators <- 1..8,
  Stake <- [i \in 1..8 |-> IF i >= 5 THEN 13 ELSE 12],
  MaxSlot <- 0,
  FastThreshold <- 80,
  SlowThreshold <- 60,
  ByzantineThreshold <- 0,
  MessageDelay <- 1,
  BlockTimeout <- 1,
  FastTimeout <- 0,
  SlowTimeout <- 0,
  blocks <- blocks,
  votes <- votes,
  certificates <- certificates,
  currentSlot <- currentSlot,
  currentTime <- currentTime,
  shreds <- shreds,
  receivedShreds <- receivedShreds,
  reconstructedBlocks <- reconstructedBlocks,
  network <- network,
  validatorState <- validatorState,
  voteHistory <- voteHistory,
  timeouts <- timeouts

Spec == M!Spec

TypeInvariant == M!TypeInvariant
NoConflictingFinalization == M!NoConflictingFinalization
ChainConsistency == M!ChainConsistency
OneCertificatePerSlot == M!OneCertificatePerSlot
NoEquivocation == M!NoEquivocation

=============================================================================
