"""Recheck source-bound historical receipt claims without running Lean."""
import hashlib,json,re

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def parse_receipt(path):
    text=path.read_text(encoding='utf-8-sig')
    # A few original console receipts prefix the JSON object with progress text.
    start=text.find('{')
    value,end=json.JSONDecoder().raw_decode(text[start:])
    suffix=text[start+end:].strip()
    # Archived console captures record their shell exit after the JSON.
    # Accept only the two observed successful trailers, consistent with the receipt.
    if suffix and not (suffix in {'EXIT 0','exit=0'} and value.get('exit_code')==0 and value.get('verified') is True):
        raise ValueError('Unexpected receipt suffix')
    return value

def validate_source_only(root,row,record,graph,toolchain):
    """Preserve a legacy compiler record without inventing its missing Mathlib pin."""
    covered=set()
    for group in record.get('source_only_receipts',[]):
        assert group['schema']=='phenotype-identification-standalone-v1'
        assert group['mathlib_manifest_recorded'] is False
        path=root/group['receipt'];assert digest(path)==group['receipt_sha256']
        verifier=root/group['verifier'];assert digest(verifier)==group['verifier_sha256']
        assert "'-DwarningAsError=true'" in verifier.read_text(encoding='utf8')
        r=parse_receipt(path);assert r['toolchain']==toolchain
        name=group['module'];source=name.replace('.','/')+'.lean'
        assert source in row['closure'] and name in graph
        # This limited format cannot authenticate local imported artifacts.
        assert graph[name]==['Mathlib']
        m=r['modules'][group['receipt_module']]
        assert m['exit_code']==0 and m['stdout']==m['stderr']==''
        assert digest(root/source)==m['sha256']==group['source_sha256']
        probe=r['axiom_probe'];assert probe['exit_code']==0 and probe['stderr']==''
        names=['PhenotypeIdentification.'+n for n in probe['declarations']]
        reports={}
        for line in probe['stdout'].splitlines():
            match=re.fullmatch(r"'([^']+)' depends on axioms: \[([^\]]*)\]",line)
            assert match and match[1] not in reports
            reports[match[1]]=[a.strip() for a in match[2].split(',') if a.strip()]
        assert set(reports)==set(names)==set(group['probed_axioms'])
        assert reports==group['probed_axioms']
        assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in reports.values())
        assert all(re.search(r'^theorem '+re.escape(n.rsplit('.',1)[-1])+r'\b',
                            (root/source).read_text(encoding='utf8'),re.M) for n in names)
        assert source not in covered;covered.add(source)
    return covered

def validate_closure_receipts(root,row,record,graph,toolchain,manifest):
    covered=set();dependency_cache={}
    def deps(name,active=None):
        active=set() if active is None else active
        assert name not in active
        if name in dependency_cache:return dependency_cache[name]
        found=set()
        for imp in graph[name]:
            if imp in graph:
                found.add(imp);found.update(deps(imp,active|{name}))
        dependency_cache[name]=found
        return found
    for group in record['receipt_closures']:
        receipt_path=root/group['receipt']
        assert digest(receipt_path)==group['receipt_sha256']
        r=parse_receipt(receipt_path)
        assert r['verified'] and r['exit_code']==0 and r['stdout']==r['stderr']==''
        assert r['lean_toolchain']==toolchain and r['lake_manifest_sha256']==manifest
        assert r['target_compilation']['warning_as_error']
        assert r['dependency_materialization']['status']=='complete'
        assert not r.get('declaration_probe_stdout') and not r.get('declaration_probe_stderr')
        name=group['root_module'];source=name.replace('.','/')+'.lean'
        assert source in row['closure'] and digest(root/source)==r['proof_sha256']
        dep_records=r['dependency_materialization']['dependencies']
        assert len(dep_records)==len({d['module'] for d in dep_records})
        assert {d['module'] for d in dep_records}==deps(name)
        hashes={name:r['proof_sha256'],**{d['module']:d['source_sha256'] for d in dep_records}}
        assert hashes==group['source_hashes']
        for module,expected in hashes.items():
            path=module.replace('.','/')+'.lean'
            assert path in row['closure'] and digest(root/path)==expected
            covered.add(path)
        interfaces=r.get('declaration_interfaces',[])
        assert {x['declaration_name'] for x in interfaces}==set(group['probed_declarations'])
        assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in interfaces)
    partial=validate_source_only(root,row,record,graph,toolchain)
    assert not covered&partial
    assert covered|partial==set(row['closure'])

def validate(root, row):
    path=row.get('historical_verification')
    if not path:return
    record=json.loads((root/path).read_text(encoding='utf8'))
    assert record['paper_id']==row['id']
    assert record['fresh_destination_run'] is False
    expected_status=('SOURCE_MATCHED_WITH_PARTIAL_ENVIRONMENT_EVIDENCE' if record.get('source_only_receipts')
                     else 'SOURCE_AND_ENVIRONMENT_MATCHED')
    assert record['status']==expected_status
    if record.get('source_only_receipts'):assert 'receipt_closures' in record
    toolchain=(root/'mathlib4_project/lean-toolchain').read_text().strip()
    manifest=digest(root/'mathlib4_project/lake-manifest.json')
    assert record['lean_toolchain']==toolchain and record['lake_manifest_sha256']==manifest
    inventory=json.loads((root/'migration/modules.json').read_text(encoding='utf8'))
    graph={m['module']:m['imports'] for m in inventory}
    if 'receipt_closures' in record:
        return validate_closure_receipts(root,row,record,graph,toolchain,manifest)
    covered=[]
    by_module={m['module']:m for m in record['modules']}
    assert len(by_module)==len(record['modules'])
    def dependencies(name,active=None):
        active=set() if active is None else active
        assert name not in active, 'Import cycle'
        result=set()
        for dep in graph[name]:
            if dep not in graph:continue
            result.add(dep);result.update(dependencies(dep,active|{name}))
        return result
    for module in record['modules']:
        source=module['source'];covered.append(source)
        assert digest(root/source)==module['source_sha256']
        assert digest(root/module['receipt'])==module['receipt_sha256']
        receipt=json.loads((root/module['receipt']).read_text(encoding='utf8'))
        assert receipt['verified'] and receipt['exit_code']==0
        assert receipt['stdout']==receipt['stderr']==''
        assert receipt['proof_sha256']==module['source_sha256']
        assert receipt['lean_toolchain']==toolchain and receipt['lake_manifest_sha256']==manifest
        assert receipt['target_compilation']['warning_as_error']
        assert receipt['dependency_materialization']['status']=='complete'
        saved=receipt['dependency_materialization']['dependencies']
        assert len(saved)==len({d['module'] for d in saved})
        required=dependencies(module['module'])
        assert {d['module'] for d in saved}==required
        assert {d['module'] for d in module['local_dependencies']}==required
        for dep in saved:
            selected=by_module[dep['module']]
            assert dep['source_sha256']==selected['source_sha256']
            declared=next(d for d in module['local_dependencies'] if d['module']==dep['module'])
            assert declared['source_sha256']==dep['source_sha256']
            dep_receipt=json.loads((root/selected['receipt']).read_text(encoding='utf8'))
            assert dep['cache_key']==dep_receipt['verified_module_artifact']['cache_key']
        interfaces=receipt['declaration_interfaces']
        assert {x['declaration_name'] for x in interfaces}==set(module['probed_declarations'])
        assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in interfaces)
    assert len(covered)==len(set(covered)) and set(covered)==set(row['closure'])
