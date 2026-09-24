"""Replay proved claims using the canonical interpreter and bounded child jobs.

Run this script itself under scripts/process_guard.py with a 600-second lease.
Discovery/optimization is not replayed. No Lean dependencies are changed.
"""
import sys,json,subprocess,hashlib,time
from pathlib import Path
W=Path(__file__).resolve().parent;ROOT=W.parents[1]

def main():
    stages=[('local generalized Hopf',['local_certificate.py']),
            ('directed finite-source defect',['finite_source.py']),
            ('Fourier existence',['sparse_fourier_pilot.py','--certify']),
            ('positive finite geometry',['finite_geometry_certificate.py']),
            ('transverse attraction',['attraction_certificate.py']),
            ('exact control algebra',['control_pilot.py'])]
    results=[];logs=W/'replay_logs';logs.mkdir(exist_ok=True)
    for name,args in stages:
        start=time.monotonic();run=subprocess.run([sys.executable,str(W/args[0]),*args[1:]],cwd=ROOT,capture_output=True,text=True,timeout=240)
        (logs/(args[0]+'.txt')).write_text(run.stdout+'\n'+run.stderr,encoding='utf-8')
        row={'stage':name,'exit_code':run.returncode,'seconds':round(time.monotonic()-start,3)};results.append(row);print(json.dumps(row),flush=True)
        (W/'replay_results.json').write_text(json.dumps({'stages':results,'all_pass':all(r['exit_code']==0 for r in results)},indent=2))
        if run.returncode:raise RuntimeError(name+' failed; inspect replay log')
    receipt=json.loads((W/'source_control.verify.json').read_text());proof=ROOT/'proofs/SwitchablePhosphorylation/SourceControlAlgebra.lean'
    assert receipt['verified'] and receipt['exit_code']==0 and not receipt['stdout'] and not receipt['stderr']
    assert receipt['proof_sha256']==hashlib.sha256(proof.read_bytes()).hexdigest()
    result={'stages':results,'all_pass':True,'Lean':'strict saved receipt matches current source; analytical theorems are C+I, not full K','python':sys.executable}
    (W/'replay_results.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
