# Solana Alpenglow Formal Verification

This repository contains a complete, reproducible formal verification of core safety theorems from the Alpenglow consensus protocol using TLA+/TLAPS, plus optional TLC model checking configs.

## Overview

Alpenglow is Solana's consensus protocol upgrade achieving dramatic improvements over TowerBFT:

- 100–150ms finalization (100x faster than current)
- Dual-path consensus: Votor enables fast finalization with 80% stake participation or conservative finalization with 60% stake
- Optimized block propagation: Rotor uses erasure coding for efficient single-hop block distribution
- "20+20" resilience: tolerates up to 20% Byzantine plus 20% crashed/offline nodes under good network conditions

For a blockchain securing billions in value, paper-only proofs are not sufficient. This repo provides machine-checkable proofs and an honest, automated workflow to reproduce results on any system.

## What’s verified (machine-checked)

- QuorumIntersection.tla: 175/175 obligations proved
- CertificateUniqueness.tla: 28/28 obligations proved
- FinalizationSafety.tla: 43/43 obligations proved

All arithmetic helper lemmas are in `proofs/StakeArithmetic.tla` and are proved without top-level axioms. FinalizationSafety reuses global intersection bounds from QuorumIntersection to keep obligations small and robust.

See VERIFICATION_RESULTS.md for exact commands and log locations.

## How to verify on your system

Option A (recommended): Docker, one command

```bash
./run-proofs-docker.sh
```

This builds a TLAPS 1.6.0-pre + Isabelle 2025 image and runs all proofs. Results are written to:

- Logs: `verification_logs/tlaps_quorumintersection_docker.log`, `tlaps_certificateuniqueness_docker.log`, `tlaps_finalizationsafety_docker.log`
- Proof certificates: `proofs/.tlacache/*`

Option B: Local TLAPS install

1) Install TLAPS 1.6.0-pre with Isabelle backend (or use the Docker image above)
2) In the repo root:

```bash
export TLA_PATH="$(pwd)/tla:$(pwd)/proofs"
tlapm -C --stretch 6 -I proofs -I tla proofs/QuorumIntersection.tla
tlapm -C --stretch 6 -I proofs -I tla proofs/CertificateUniqueness.tla
tlapm -C --stretch 6 -I proofs -I tla proofs/FinalizationSafety.tla
```

Capture logs if desired:

```bash
mkdir -p verification_logs
tlapm -C --stretch 6 -I proofs -I tla proofs/QuorumIntersection.tla \
  2>&1 | tee verification_logs/tlaps_quorum_local.log
```

## Optional: TLC model checking

Configs under `configs/` support small-node model checking for sanity/liveness exploration with standard TLA+ tools. TLC is not required to reproduce the safety proofs above.

### Quick TLC smoke tests (wrappers)

Run invariants-only, one-state smoke checks for 4/6/8/10 validators via wrapper modules:

```bash
./run-tlc-docker.sh wrappers
```

This invokes `tla/MC_Full_{4,6,8,10}val_fast.tla` which instantiate `AlpenglowFull` with `MaxSlot=0` and zero timeouts. Logs are saved to `verification_logs/tlc_results/`.

## Repository layout

- `tla/` — core TLA+ specs (AlpenglowCore, etc.)
- `proofs/` — TLAPS safety proof modules and `.tlacache/` certificates
- `configs/` — TLC model checker configs (optional)
- `run-proofs-docker.sh` — build and run proofs in Docker
- `VERIFICATION_RESULTS.md` — exact, reproducible results and commands

## License

Apache-2.0 (see LICENSE)
