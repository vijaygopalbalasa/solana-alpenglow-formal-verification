# Alpenglow Formal Verification — Report

All claims are machine‑checked and reproducible. This report summarizes results, lists proof status per theorem, and provides exact reproduction steps.

## Executive summary

- Safety proofs (TLAPS): All theorems fully proved and re‑checked with Isabelle
  - QuorumIntersection.tla — 175/175 obligations proved
  - CertificateUniqueness.tla — 28/28 obligations proved
  - FinalizationSafety.tla — 43/43 obligations proved
- Model checking (TLC): Sanity evidence across 4/6 (deep from earlier logs) and 4/6/8/10 (fast wrappers)
  - Deep exploration: 4‑validator (≈940K states), 6‑validator (≈444K states) — no violations
  - Fast wrappers: MC_Full_{4,6,8,10}val_fast — invariants hold in 1‑state smoke runs

## Proof status by module and key lemmas

1) QuorumIntersection.tla — 175/175
   - Core idea: Any two quorums overlap in at least 40% stake under 20% Byzantine bound
   - Uses arithmetic helpers from `proofs/StakeArithmetic.tla`

2) CertificateUniqueness.tla — 28/28
   - Ensures at most one certificate per (slot) and no conflicting finalized blocks
   - Relies on intersection properties established above

3) FinalizationSafety.tla — 43/43
   - Simplified to reuse global intersection bounds (no local heavy lemmas)
   - ByzSubset/Stake bounds instantiated; arithmetic helpers (e.g., FastMarginStrict, SlowMarginGe) used

Arithmetic helpers (all proved): `proofs/StakeArithmetic.tla` — monotonicity, subset, and threshold margin lemmas.

## Reproducibility (Docker)

Proofs:

```bash
./run-proofs-docker.sh
```

Outputs:
- Logs: `verification_logs/tlaps_quorumintersection_docker.log`, `tlaps_certificateuniqueness_docker.log`, `tlaps_finalizationsafety_docker.log`
- Proof certificates: `proofs/.tlacache/*`

Model checking (optional):

```bash
./run-tlc-docker.sh wrappers   # runs MC_Full_{4,6,8,10}val_fast
```

Deep exploration logs (earlier session):
- `verification_logs/tlc_results/AlpenglowMC_4val_20251007_184957.log` (~940K states)
- `verification_logs/tlc_results/AlpenglowMC_6val_20251007_184630.log` (~444K states)

## Toolchain

- TLAPS: 1.6.0‑pre (commit 386cb32)
- Isabelle: 2025
- TLC: 2.19
- Java (Docker): OpenJDK 21

## Artefacts

- `proofs/` — proof modules and `.tlacache/`
- `tla/` — core TLA+ specs (AlpenglowFull + wrappers)
- `VERIFICATION_RESULTS.md` — commands and final counts
- `verification_logs/` — logs from runs
- `configs/` — optional TLC configs
