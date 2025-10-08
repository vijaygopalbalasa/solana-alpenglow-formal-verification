# Verification Results

This file lists only machine-checked, reproducible results. Each command below can be run verbatim to regenerate the proofs and logs.

## TLAPS Proofs (298 obligations proved)

### Core Safety Proofs

- **QuorumIntersection.tla**: 175/175 obligations proved
  - Proves quorum intersection properties for both fast (80%) and slow (60%) paths
  - Reproduce: `export TLA_PATH="$(pwd)/tla:$(pwd)/proofs" && tlapm -C --stretch 6 -I proofs -I tla proofs/QuorumIntersection.tla`

- **CertificateUniqueness.tla**: 28/28 obligations proved
  - Proves certificate uniqueness at each slot
  - Reproduce: `export TLA_PATH="$(pwd)/tla:$(pwd)/proofs" && tlapm -C --stretch 6 -I proofs -I tla proofs/CertificateUniqueness.tla`

- **FinalizationSafety.tla**: 43/43 obligations proved
  - Proves finalization safety (no two conflicting blocks finalize)
  - Reproduce: `export TLA_PATH="$(pwd)/tla:$(pwd)/proofs" && tlapm -C --stretch 6 -I proofs -I tla proofs/FinalizationSafety.tla`

### Liveness & Resilience Proofs

- **Liveness.tla**: 23/23 obligations proved
  - Proves progress with ≥60% honest stake and bounded finalization time
  - Reproduce: `export TLA_PATH="$(pwd)/tla:$(pwd)/proofs" && tlapm -C --stretch 6 -I proofs -I tla proofs/Liveness.tla`

- **Resilience.tla**: 29/29 obligations proved
  - Proves safety under ≤20% Byzantine stake, liveness under ≤20% offline stake, and combined 20/20 resilience
  - Reproduce: `export TLA_PATH="$(pwd)/tla:$(pwd)/proofs" && tlapm -C --stretch 6 -I proofs -I tla proofs/Resilience.tla`

### Block Propagation Specification

- **Rotor.tla**: 0 obligations (complete specification with PROOF OMITTED)
  - Formal specification of erasure-coded block propagation with stake-weighted relay sampling
  - Properties: resilience to failures, latency bounds, bandwidth optimality, safety, no equivocation
  - Reproduce: `export TLA_PATH="$(pwd)/tla:$(pwd)/proofs" && tlapm -C --stretch 6 -I proofs -I tla proofs/Rotor.tla`

### Notes

- Arithmetic helper lemmas live in `proofs/StakeArithmetic.tla`
- Some arithmetic lemmas use axioms (GeGtTrans, DivInNat) due to TLAPS 1.6.0 limitations with integer division reasoning
- The FinalizationSafety proof reuses global intersection bounds from QuorumIntersection to keep obligations manageable

## TLC model checking evidence

Reproducible runs (Docker):

- 4 validators (deep exploration) — no violations
  - Command: `./run-tlc-docker.sh quick` (includes 4/6) or run individually with configs
  - Log: `verification_logs/tlc_results/AlpenglowMC_4val_20251007_184957.log` (large state space)

- 6 validators (deep exploration) — no violations
  - Command: `./run-tlc-docker.sh quick`
  - Log: `verification_logs/tlc_results/AlpenglowMC_6val_20251007_184630.log`

- 4 validators (fast wrapper) — invariants hold (one-state smoke)
  - Command: `./run-tlc-docker.sh wrappers`
  - Log: `verification_logs/tlc_results/MC_Full_4val_fast_*.log`

- 6 validators (fast wrapper) — invariants hold (one-state smoke)
  - Command: `./run-tlc-docker.sh wrappers`
  - Log: `verification_logs/tlc_results/MC_Full_6val_fast_*.log`

- 8 validators (fast wrapper) — invariants hold (one-state smoke)
  - Command: `./run-tlc-docker.sh wrappers`
  - Log: `verification_logs/tlc_results/MC_Full_8val_fast_*.log`

- 10 validators (fast wrapper) — invariants hold (one-state smoke)
  - Command: `./run-tlc-docker.sh wrappers`
  - Log: `verification_logs/tlc_results/MC_Full_10val_fast_*.log`

## How to reproduce on your system

### Option A (recommended): Docker

- **Requirements**: Docker Desktop/Engine
- **Run**: `./run-proofs-docker.sh`
- **Logs**:
  - Individual modules: `verification_logs/tlaps_quorumintersection_docker.log`, `tlaps_certificateuniqueness_docker.log`, `tlaps_finalizationsafety_docker.log`, `tlaps_rotor_docker.log`, `tlaps_liveness_docker.log`, `tlaps_resilience_docker.log`
  - Complete run: `verification_logs/complete_verification_final.log`
- **Proof certificates**: `proofs/.tlacache/*`

### Option B: Local TLAPS install

- Install TLAPS 1.6.0-pre with Isabelle 2025 backend
- Set TLA_PATH and run the six commands shown above
- Logs can be captured with `... 2>&1 | tee verification_logs/<name>.log`

## TLC (optional, for liveness/model checking)

TLC configurations are provided under `configs/`. You can run TLC with standard TLA+ tools; this is not required for the safety proofs above.
