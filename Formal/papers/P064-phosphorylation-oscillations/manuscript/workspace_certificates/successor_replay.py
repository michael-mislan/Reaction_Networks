"""Replay the final paper's certificate chain, without discovery searches."""
from pathlib import Path
import subprocess,sys,json,time,hashlib
P=Path(__file__).resolve().parent
def main():
    rows=[]
    for args in [['certify_one_pool.py','--compressed'],['audit_literal_source.py'],['certify_nonlinear_reduction.py','--attracting'],['certify_resources.py'],['certify_measurement.py','--practical']]:
        start=time.monotonic();result=subprocess.run([sys.executable,str(P/args[0]),*args[1:]],capture_output=True,text=True,timeout=120)
        row={'command':args,'exit_code':result.returncode,'seconds':time.monotonic()-start,'stdout':result.stdout,'stderr':result.stderr,'producer_sha256':hashlib.sha256((P/args[0]).read_bytes()).hexdigest()}
        rows.append(row);print(args,result.returncode,flush=True)
        if result.returncode:break
    ok=len(rows)==5 and all(x['exit_code']==0 for x in rows)
    (P/'successor_replay_results.json').write_text(json.dumps({'all_passed':ok,'rows':rows},indent=2))
    if not ok:raise SystemExit(1)
if __name__=='__main__':main()
