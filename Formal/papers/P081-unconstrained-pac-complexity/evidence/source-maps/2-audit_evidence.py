"""Read-only source/receipt audit; does not recompile Lean or publish status."""
import hashlib,json
from pathlib import Path
from datetime import datetime
p=Path(__file__).resolve().parent
repo=p.parents[2]
campaign=p.parent/'campaign_2026_09_05'
records=[]
for name in ['complexity_root.verify.json','balanced_example.verify.json','formula_dense_size.verify.json']:
    receipt=json.loads((campaign/name).read_text(encoding='utf-8-sig'))
    assert receipt['verified'] and receipt['exit_code']==0
    assert '-DwarningAsError=true' in receipt['command']
    assert not receipt['stdout'].strip() and not receipt['stderr'].strip()
    files=[dict(source=receipt['proof'],source_sha256=receipt['proof_sha256'])]+receipt['dependency_materialization']['dependencies']
    for f in files:
        assert hashlib.sha256(Path(f['source']).read_bytes()).hexdigest()==f['source_sha256'],f['source']
        if f.get('artifact'):
            assert hashlib.sha256(Path(f['artifact']).read_bytes()).hexdigest()==f['artifact_sha256'],f['artifact']
    for i in receipt['declaration_interfaces']:
        assert set(i['axioms'])<= {'propext','Classical.choice','Quot.sound'}
    assert (repo/'mathlib4_project/lean-toolchain').read_text().strip()==receipt['lean_toolchain']
    assert hashlib.sha256((repo/'mathlib4_project/lake-manifest.json').read_bytes()).hexdigest()==receipt['lake_manifest_sha256']
    records.append(dict(receipt=name,source_files_checked=len(files),strict=True,source_hash=receipt['proof_sha256'],declarations=[dict(name=i['declaration_name'],type=i['elaborated_type'],axioms=i['axioms']) for i in receipt['declaration_interfaces']]))
out=dict(status='PASS',timestamp=datetime.now().astimezone().isoformat(),method='Hash and strict receipt audit; not a fresh clean rebuild',records=records)
(p/'evidence_audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status=out['status'],source_checks=sum(r['source_files_checked'] for r in records))))
