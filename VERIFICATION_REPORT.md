# Alpenglow Formal Verification — Report

This report states what is proved, how to reproduce the proofs, and where to find artefacts. All claims are machine‑checked and reproducible from this repository.

## What is proved (safety)

- QuorumIntersection.tla — 175/175 obligations proved
- CertificateUniqueness.tla — 28/28 obligations proved
- FinalizationSafety.tla — 43/43 obligations proved

Arithmetic lemmas are in `proofs/StakeArithmetic.tla` and use OBVIOUS steps (no top‑level axioms). FinalizationSafety reuses global bounds from QuorumIntersection.

## How to reproduce

Docker:

```bash
./run-proofs-docker.sh
```

Outputs:
- Logs: `verification_logs/tlaps_quorumintersection_docker.log`, `tlaps_certificateuniqueness_docker.log`, `tlaps_finalizationsafety_docker.log`
- Proof certificates: `proofs/.tlacache/*`

Local TLAPS:

```bash
export TLA_PATH="$(pwd)/tla:$(pwd)/proofs"
tlapm -C --stretch 6 -I proofs -I tla proofs/QuorumIntersection.tla
tlapm -C --stretch 6 -I proofs -I tla proofs/CertificateUniqueness.tla
tlapm -C --stretch 6 -I proofs -I tla proofs/FinalizationSafety.tla
```

## Toolchain

- TLAPS: 1.6.0‑pre (commit 386cb32)
- Isabelle: 2025
- Java (Docker): OpenJDK 21

## Artefacts

- `proofs/` — proof modules and `.tlacache/`
- `tla/` — core TLA+
- `VERIFICATION_RESULTS.md` — commands and final counts
- `verification_logs/` — logs from runs
- `configs/` — optional TLC configs
