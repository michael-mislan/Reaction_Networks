"""Independent execution entry point; recompute, never trust saved result hashes."""
from core_certificate import certify
from pathlib import Path
import subprocess,sys,json

r=certify()
assert (r['numerator'],r['denominator'],r['lambda_integer'])==(2147232289,2147483648,3216)
subprocess.run([sys.executable,str(Path(__file__).with_name('coupling_preflight.py'))],check=True)
print(json.dumps(dict(ok=True,core=r,trust_boundary='Exact NumPy int64 recurrence plus conventional proof; not Lean kernel replay'),indent=2))
