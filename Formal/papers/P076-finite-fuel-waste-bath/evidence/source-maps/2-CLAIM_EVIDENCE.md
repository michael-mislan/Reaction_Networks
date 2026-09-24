# Publication claim-to-evidence summary

| Claim | Status and evidence |
|---|---|
| General finite-bath operational theorem | Lean PASS: `Mission.finite_bath_horizon`, original `Resolution.verify.json` closure |
| Pure inverse design and 100-cycle example | Lean PASS: `InverseDesign.pure_inverse_design`, `MissionExample.example_mission` |
| Actual full-history product bound and every-prefix inventory | Lean PASS: `FullProduct`, `BathPrefixes`, `Sizing` |
| Terminal-stock synthesis improvement | Lean PASS: `ProductionCorollaries.verify.json`; example net synthesis >=164285714343 |
| Correlated pure-bath intensity and smaller stopped counter tail | Lean PASS: `SharpService.verify.json` |
| Halved reservoir at unchanged joint confidence | **CLOSED 19 Sep 2026** — Lean PASS: `SharpCycle.verify.json` (sharp literal-cycle joint success through the strict stopped-to-physical transfer), `SharpMission.verify.json` (conditional-history propagation, sharp prefix tolerance, `sharp_example_mission`), `SharpResolution.verify.json` (`sharp_hundred_halved_bath`: V=2e11, R=2e13, failure <= 1e-13) |
| Unrounded phase rate `kappa = 1839/8750000000000` propagated | Lean PASS: `SharpPhase.verify.json`, `SharpPhaseCycle.verify.json`, `SharpEnvelope.verify.json` (envelope + absorption from V >= 1e10), `SharpGeneral.verify.json` (full mission, every admitted bath) |
| Reduced certified instance V=9.6e10, R=9.6e12 at confidence 0.999979 | Lean PASS: `SharpMission.sharp_example_mission`; fair-comparison caveat (output scales with V) stated in the paper |
| Fixed-budget inequalities and exact endpoint bath energies | Conventional proofs in paper, based on compiled mission, potential and inventory |
| Finite metered food | Lean no-stockout/rate agreement plus explicit conventional path coupling |
| Four new ODE comparisons and six preserved original runs | Deterministic diagnostics only |
| Positive net fuel-consumption lower bound | Not established or assumed; zero drive belongs to the operational class |
| Canonical AGC publication | Not claimed; CURRENT checkpoint is distinct from the known NO_OPEN_FRONTIER publication limit |
