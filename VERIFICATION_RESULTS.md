# Verification Results

This file lists only machine-checked, reproducible results. Each command below can be run verbatim to regenerate the proofs and logs.

## TLAPS safety proofs (fully proved)

- QuorumIntersection.tla: 175/175 obligations proved
  - Reproduce: `export TLA_PATH="$(pwd)/tla:$(pwd)/proofs" && tlapm -C --stretch 6 -I proofs -I tla proofs/QuorumIntersection.tla`

- CertificateUniqueness.tla: 28/28 obligations proved
  - Reproduce: `export TLA_PATH="$(pwd)/tla:$(pwd)/proofs" && tlapm -C --stretch 6 -I proofs -I tla proofs/CertificateUniqueness.tla`

- FinalizationSafety.tla: 43/43 obligations proved
  - Reproduce: `export TLA_PATH="$(pwd)/tla:$(pwd)/proofs" && tlapm -C --stretch 6 -I proofs -I tla proofs/FinalizationSafety.tla`

Notes:
- Arithmetic helper lemmas live in `proofs/StakeArithmetic.tla` and are proved with OBVIOUS steps (no top-level axioms).
- The FinalizationSafety proof uses the global intersection bounds from `QuorumIntersection.tla` to avoid heavy local lemmas.

## How to reproduce on your system

Option A (recommended): Docker
- Requirements: Docker Desktop/Engine
- Run: `./run-proofs-docker.sh`
- Logs: `verification_logs/tlaps_quorumintersection_docker.log`, `tlaps_certificateuniqueness_docker.log`, `tlaps_finalizationsafety_docker.log`
- Proof certificates: `proofs/.tlacache/*`

Option B: Local TLAPS install
- Install TLAPS 1.6.0-pre with Isabelle 2025 backend (or use the TLAPS inside the Docker image)
- Set TLA_PATH and run the three commands shown above
- Logs can be captured with `... 2>&1 | tee verification_logs/<name>.log`

## TLC (optional, for liveness/model checking)

TLC configurations are provided under `configs/`. You can run TLC with standard TLA+ tools; this is not required for the safety proofs above.
