# Verification scope

The formal sources use Lean 4.30.0 with the revisions pinned in
[lake-manifest.json](mathlib4_project/lake-manifest.json). Per-paper claim maps
identify the declarations associated with manuscript results. A checked declaration
establishes its formal statement under its assumptions and axiom dependencies;
it does not establish every statement in the associated paper.

The saved [compilation and axiom-audit records](migration/clean-verification.json)
cover 3,566 modules and 855 per-paper declaration entries, with complete recorded
checks for 58 papers. The collection contains 5,748 production modules across
82 papers. Other results have source-era verification reports with their own
coverage and environment qualifications. These records were produced before the
present directory reorganization; no new full compilation is claimed here.

The singleton-splice module was moved into `proofs/TypeIIL`, and its direct
importer was updated. Mathematical statements and proof bodies are unchanged.
The [source-edit record](migration/source-edits.json) identifies the exact changes;
older compilation receipts retain their original paths and hashes. Dependency
versions remain pinned. File hashes and local imports are checked by
`scripts/check_integrity.py`. Those checks are not Lean compilation. Full Linux
reproduction has not been performed.

P017 and P040 include finite computations with native-evaluation axioms; their
claim maps and reports identify the relevant trust bases. P064, P079 and P082
combine formal algebra with explicitly distinguished conventional or numerical
arguments. P075 includes a historical record with partial environment evidence.
P005's [erratum](../ERRATA.md) clarifies two results that are proved conventionally.

Follow the [build guide](BUILD.md) to verify a selected paper. Shared modules occur
in more than one paper, so module counts are not counts of independent results.

The [targeted relocation check](migration/typeii-relocation-check.json) compiled
`proofs.TypeIIL.SingletonSplice` and its direct importer
`proofs.TypeIIL.SourceBackFirstWeakClosure` with warnings treated as errors.
Both passed with no compiler output. Unchanged dependencies were reused only
after checking their source and compiled-artifact hashes against the saved clean
verification records. No other Lean modules were recompiled for this change.

P064 now also includes the all-site attracting Hopf theorem for every n ≥ 3. Its saved strict receipt and all 142 source hashes match the included sources and pinned environment; no new Lean compilation was needed. See the [P064 notes](papers/P064-phosphorylation-oscillations/README.md) for the exact scope.

Machine-account names in archived command paths are redacted in the distributed receipts. Source, dependency and compiled-artifact hashes retain their original values.
