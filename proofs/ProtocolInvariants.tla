---- MODULE ProtocolInvariants ----
EXTENDS FinalizationSafety

THEOREM ProtocolFinalizationSafety ==
    NoConflictingFastCertificates /\ NoConflictingFinalCertificates
PROOF BY NoConflictingFastCertificates, NoConflictingFinalCertificates

====
