"""Compile the declared finite-algebra Lean subset and probe its axioms.

Writes lean_receipt.json.  Requires the pinned Lean 4.30.0 toolchain and the
frozen Mathlib build used by this repository; paths are taken from the
environment so the script is not tied to one machine.

  LEAN_BIN      path to lean.exe            (default: elan toolchain for v4.30.0)
  MATHLIB_ROOT  directory holding .lake/packages (default: ../../../mathlib4_project)
  PROOF_ROOT    the -R root for `proofs.*` modules (default: three levels up)
"""
import os, json, subprocess, hashlib, tempfile, shutil
from pathlib import Path
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN = Path(os.environ.get('LEAN_BIN', Path.home() /
            '.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean.exe'))
MROOT = Path(os.environ.get('MATHLIB_ROOT', REPO / 'mathlib4_project'))
PROOT = Path(os.environ.get('PROOF_ROOT', REPO))
MODULES = ['Resolution', 'Resolvent', 'DelayedChannel', 'OffspringOrder', 'CancelledTarget']
PROBE = ['marker_offdiagonal', 'marker_determinant', 'cancelled_target',
         'mixture_calibration', 'contamination_bound', 'six_category_features']

pkgs = ['Cli', 'LeanSearchClient', 'Qq', 'aesop', 'batteries', 'importGraph',
        'mathlib', 'plausible', 'proofwidgets']
paths = [MROOT / '.lake/build/lib/lean'] + [MROOT / '.lake/packages' / p / '.lake/build/lib/lean'
                                            for p in pkgs]
env = dict(os.environ, LEAN_PATH=';'.join(str(p) for p in paths))
assert LEAN.exists(), 'lean binary not found: %s' % LEAN

out = dict(timestamp=datetime.now(timezone.utc).isoformat(), lean=str(LEAN),
           toolchain=(MROOT / 'lean-toolchain').read_text().strip(), modules={})
tmp = Path(tempfile.mkdtemp(prefix='leanchk'))
try:
    stage = tmp / 'proofs' / 'PhenotypeIdentification'
    stage.mkdir(parents=True)
    for m in MODULES:
        src = PROOT / 'proofs/PhenotypeIdentification' / (m + '.lean')
        cmd = [str(LEAN), '-DwarningAsError=true', '-R', str(PROOT),
               '-o', str(stage / (m + '.olean')), str(src)]
        env2 = dict(env, LEAN_PATH=str(tmp) + ';' + env['LEAN_PATH'])
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=1200, env=env2)
        out['modules'][m] = dict(exit_code=r.returncode,
                                 sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
                                 stdout=r.stdout.strip(), stderr=r.stderr.strip())
        print(m, 'exit', r.returncode, r.stdout.strip()[:400])
        assert r.returncode == 0, m

    probe = tmp / 'probe.lean'
    probe.write_text('import proofs.PhenotypeIdentification.CancelledTarget\n' +
                     ''.join('#print axioms PhenotypeIdentification.%s\n' % d for d in PROBE),
                     encoding='utf-8')
    env2 = dict(env, LEAN_PATH=str(tmp) + ';' + env['LEAN_PATH'])
    r = subprocess.run([str(LEAN), '-R', str(tmp), str(probe)],
                       capture_output=True, text=True, timeout=1200, env=env2)
    out['axiom_probe'] = dict(exit_code=r.returncode, stdout=r.stdout.strip(),
                              stderr=r.stderr.strip(), declarations=PROBE)
    print(r.stdout, r.stderr)
    assert r.returncode == 0, 'axiom probe failed'
    assert 'sorry' not in r.stdout.lower(), 'a declaration depends on sorryAx'
    assert r.stdout.count("'axioms'") + r.stdout.count('axioms') >= len(PROBE), \
        'probe did not report every declaration'
finally:
    shutil.rmtree(tmp, ignore_errors=True)

out['scope'] = ('Finite algebra only. No stochastic path, resolvent integral, '
                'concentration inequality, interval-arithmetic claim or '
                'comparison principle is formalized.')
(HERE / 'lean_receipt.json').write_text(json.dumps(out, indent=1))
print('receipt written to lean_receipt.json')
