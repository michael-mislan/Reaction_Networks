"""Check copied bytes, import closure, module coverage and local Markdown links."""
from pathlib import Path
import argparse,json,hashlib,re,sys,urllib.parse
ROOT=Path(__file__).resolve().parents[1]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()

def reading_copy_matches(root, entry):
 pdf=root/entry['pdf'];source=root/entry['source']
 return (pdf.is_file() and source.is_file() and
         sha(pdf)==entry['sha256'] and sha(source)==entry['sha256'])
def main():
 p=argparse.ArgumentParser();p.add_argument('--source',type=Path,help='Optional original source for read-only snapshot comparison');args=p.parse_args()
 files=json.loads((ROOT/'migration/files.json').read_text(encoding='utf8'));errors=[]
 portable=ROOT/'migration/portable-scripts.json'
 if portable.exists():
  for item in json.loads(portable.read_text(encoding='utf8'))['scripts']:
   try:
    original=(ROOT/item['source']).read_bytes();derived=(ROOT/item['destination']).read_bytes()
    if hashlib.sha256(original).hexdigest()!=item['source_sha256'] or hashlib.sha256(derived).hexdigest()!=item['destination_sha256']:
     errors.append('Portable-script hash mismatch: '+item['destination'])
    expected_script=original
    for replacement in item['replacements']:
     old=replacement['old'].encode();new=replacement['new'].encode()
     if expected_script.count(old)!=1:errors.append('Ambiguous portable-script replacement: '+item['destination'])
     expected_script=expected_script.replace(old,new)
    if expected_script!=derived:errors.append('Unexpected portable-script edit: '+item['destination'])
   except (OSError,KeyError,ValueError) as exc:errors.append('Portable-script validation failed: '+str(exc))
 for f in files:
  target=ROOT/f['destination']
  if not target.is_file() or sha(target)!=f['sha256']:errors.append('Copied-byte mismatch: '+f['destination'])
  if args.source:
   src=args.source/f['source']
   if not src.is_file() or sha(src)!=f.get('original_sha256',f['sha256']):errors.append('Source snapshot changed: '+f['source'])
 modules=json.loads((ROOT/'migration/modules.json').read_text(encoding='utf8'));names={m['module'] for m in modules}
 expected={m['module'].replace('.','/')+'.lean' for m in modules}
 actual={f.relative_to(ROOT).as_posix() for folder in ['proofs','problem_workspaces'] for f in (ROOT/folder).rglob('*.lean')}
 if expected!=actual:errors.append('Lean coverage mismatch: '+str(sorted(expected^actual)))
 external={'Mathlib','Batteries','Aesop','Qq','Lean','Init','Std','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Lake','Cli'}
 lower={f.lower():f for f in actual}
 if len(lower)!=len(actual):errors.append('Case-colliding source paths')
 for m in modules:
  for imp in m['imports']:
   if imp not in names and imp.split('.')[0] not in external:errors.append('Unresolved import '+imp+' from '+m['module'])
   if imp in names:
    path=imp.replace('.','/')+'.lean'
    if path not in actual:errors.append('Import case mismatch: '+path)
 rows=json.loads((ROOT/'migration/papers.json').read_text(encoding='utf8'))
 from paper_inventory import inventory
 try: inventory(rows)
 except (ValueError, KeyError, OSError) as exc: errors.append(str(exc))
 claim_count=0
 presentation_path=ROOT/'migration/presentation-pdfs.json'
 presentations=json.loads(presentation_path.read_text(encoding='utf8')).get('papers',[]) if presentation_path.exists() else []
 paper_dirs={r['id']:r['directory'] for r in rows}
 seen_presentations=set()
 for item in presentations:
  pid=item['paper_id'];base=paper_dirs.get(pid)
  if pid in seen_presentations or not base or item['source']!=base+'/paper.pdf' or item['presentation']!=base+'/presentation.pdf':
   errors.append('Invalid presentation PDF mapping: '+pid);continue
  seen_presentations.add(pid)
  for field in ['source','presentation']:
   path=ROOT/item[field]
   if not path.is_file() or sha(path)!=item[field+'_sha256']:errors.append('Presentation PDF hash mismatch: '+item[field])
  if item.get('author_metadata')!='' or item.get('validation',{}).get('status')!='PASS':errors.append('Unvalidated presentation PDF: '+pid)
 expected_presentations={item['presentation'] for item in presentations}
 actual_presentations={path.relative_to(ROOT).as_posix() for path in ROOT.glob('papers/*/presentation.pdf')}
 if expected_presentations!=actual_presentations:errors.append('Presentation PDF inventory mismatch: '+str(sorted(expected_presentations^actual_presentations)))
 for row in rows:
  from historical_evidence import validate as validate_history
  try: validate_history(ROOT,row)
  except (AssertionError,ValueError,KeyError,OSError) as exc:errors.append('Historical evidence mismatch: '+row['id']+' '+str(exc))
  base=ROOT/row['directory']
  for required in ['paper.pdf','README.md','claims.json','evidence/migration.json']:
   if not (base/required).is_file():errors.append('Missing paper artifact: '+row['id']+'/'+required)
  claims=json.loads((base/'claims.json').read_text(encoding='utf8'))['formal_claims']
  if len({c['declaration'] for c in claims})!=len(claims):errors.append('Repeated declaration identity: '+row['id'])
  closure=set(row['closure']);claim_count+=len(claims)
  for claim in claims:
   module=claim['module'];source=claim['source']
   if module not in names or source not in closure or source!=module.replace('.','/')+'.lean':
    errors.append('Claim outside inventoried paper closure: '+row['id']+' '+claim['declaration'])
   evidence=claim.get('evidence')
   if evidence and not (ROOT/evidence).is_file():errors.append('Missing claim evidence: '+row['id']+' '+evidence)
   for entry in claim.get('publication_entry_points',[]):
    if entry['module'] not in names or entry['source'] not in closure or entry['source']!=entry['module'].replace('.','/')+'.lean':errors.append('Invalid declaration exposure: '+row['id']+' '+claim['declaration'])
    if entry.get('evidence') and not (ROOT/entry['evidence']).is_file():errors.append('Missing exposure evidence: '+row['id']+' '+entry['evidence'])
 # Only generated public navigation is checked here. Historical source maps
 # retain their old relative links and are explicitly labelled archival.
 pages=[ROOT/'README.md',ROOT/'BUILD.md',ROOT/'RIGHTS.md',ROOT/'CITATION.md',ROOT/'VERIFICATION.md',*ROOT.glob('papers/*/README.md')]
 library=json.loads((ROOT/'migration/library.json').read_text(encoding='utf8'))['papers']
 taxonomy=json.loads((ROOT/'migration/taxonomy.json').read_text(encoding='utf8'))
 if {e['id'] for e in library}!={r['id'] for r in rows} or len(library)!=len(rows):errors.append('Reading library paper coverage mismatch')
 expected_pdfs=set()
 for entry in library:
  expected_pdfs.add(entry['pdf']);pdf=ROOT/entry['pdf']
  if not pdf.name.startswith(entry['id']+'-'):errors.append('Missing global PDF number: '+entry['pdf'])
  if not reading_copy_matches(ROOT,entry):errors.append('Reading copy differs from validated source: '+entry['id'])
  assignment=taxonomy['papers'][entry['id']]
  expected_folder='../'+taxonomy['categories'][assignment['primary']]['folder']
  if pdf.parent.resolve()!=(ROOT/expected_folder).resolve() or entry['tags']!=assignment['tags']:errors.append('Reading taxonomy mismatch: '+entry['id'])
 if expected_pdfs!={'../'+p.relative_to(ROOT.parent).as_posix() for branch in ['Theory','Applications'] for p in (ROOT.parent/branch).rglob('*.pdf')}:errors.append('Unexpected or missing reading-library PDF')
 pages += [ROOT.parent/'README.md',ROOT.parent/'TAGS.md',ROOT.parent/'RIGHTS.md',ROOT.parent/'CITATION.md',ROOT.parent/'ERRATA.md',ROOT.parent/'RESEARCH_NOTES.md'] + [p for branch in ['Theory','Applications'] for p in (ROOT.parent/branch).rglob('*.md')]
 for page in pages:
  for link in re.findall(r'\]\(([^)]+)\)',page.read_text(encoding='utf8')):
   if '://' in link or link.startswith('#'):continue
   link=urllib.parse.unquote(link.split('#')[0]).strip('<>')
   if not (page.parent/link).exists():errors.append('Broken link '+str(page)+': '+link)
 report={'library_pdfs':len(library),'library_categories':len(taxonomy['categories']),'copied_files':len(files),'presentation_pdfs':len(presentations),'production_modules':len(modules),'papers':len(rows),'mapped_declarations':claim_count,'copied_bytes':sum(f['bytes'] for f in files),'source_compared':bool(args.source),'errors':errors,'status':'PASS' if not errors else 'FAIL','meaning':'Copy integrity, presentation hashes, declared local-import closure, claim inventory coverage and navigation checks only; not Lean compilation or semantic correspondence verification.'}
 (ROOT/'migration/integrity.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf8');print(json.dumps(report,indent=2));return bool(errors)
if __name__=='__main__':raise SystemExit(main())
