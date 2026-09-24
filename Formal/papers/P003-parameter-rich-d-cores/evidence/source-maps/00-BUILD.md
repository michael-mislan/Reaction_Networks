# D-unstable-core counterexample paper: sources and build

Canonical editable source: `d_unstable_cores_counterexample.tex` (self-contained;
the bibliography is an inline `thebibliography`, so no BibTeX pass is needed).

Delivered PDF (copied from this folder after compilation):
`E:\Erdos Problems\key_results\RAFs\D_Unstable_Cores_Counterexample_Parameter_Rich_Networks.pdf`

## Compile (genuine LaTeX build)

No TeX distribution is on the PATH of this machine, but a Tectonic engine is
present locally (bundled with a Codex plugin). From this folder:

```powershell
& 'C:\Users\researcher\.codex\.tmp\bundled-marketplaces\openai-bundled\plugins\latex\bin\tectonic.exe' -X compile --keep-logs --outdir . d_unstable_cores_counterexample.tex
```

Tectonic fetches any missing TeX packages/fonts into its own cache on first use
(network required the first time only). On a host with TeX Live or MiKTeX the
same file compiles with two passes of `pdflatex`.

The 2026-09-07 build used Tectonic 0.17.0; the log is
`d_unstable_cores_counterexample.log` (no overfull boxes; the only warnings are
hyperref bookmark notes for math in one heading and the harmless
"inputenc ignored with utf8 engines" notice).

## Independent exact re-check of the witness data

`verify_witness.py` (SymPy) re-derives, over exact rationals and Q(i):

- `S f = 0` for `f = (2,3,2,2,2)`, reactant support = negative entries of `S`;
- the exact Jacobian, the eigenpair `lambda = 1/500 + 51/500 i` with the
  Gaussian-integer eigenvector, and the factored characteristic polynomial;
- the enumeration of all 24 child selections and the 4 maximal ones;
- the three PSD weighted-symmetrization certificates, the cubic factorization
  `X (X + 4 d0) (X + 4 d1 + 2 d2)` of the exceptional child, the two
  exceptional faces, and a random-scaling numerical sanity check;
- the generalized-mass-action exponents `c_jm = R_jm / f_j` used in the paper.

```powershell
python verify_witness.py
```

## Formal source of truth

The mathematical content is the strict Lean theorem
`DUnstableCores.parameterRich_consistent_core_necessity_fin4_fin5_false` in
`proofs/DUnstableCores/ParameterRichCounterexample.lean` (proof SHA-256
`387eabbd…3d87f`, receipt `../parameter_consistent_counterexample_verify.json`).
Edit the paper only in ways consistent with that file; the paper uses the same
0-based species/reaction indexing as the Lean development.

## Editing notes

- Authorship is deliberately left blank in `\author{}`; fill it in before
  submission. The `\date` is set to September 2026.
- Citation of the refuted statement: Vassena & Stadler, Proc. R. Soc. A 480
  (2024) 20230694, Conjecture 17 (arXiv:2308.11486v3). The conjecture text is
  quoted verbatim in the introduction.
- The companion mass-action manuscript is cited as `Companion2026`; update that
  entry once it has a stable identifier.
