"""Print fresh axiom reports for claims whose complete destination build passed."""
from pathlib import Path
import argparse,json,os,re,subprocess,sys,datetime
from verify import ROOT,ENV,LOCAL,load,save,digest,run,available_mb,current_results,environment_hash,project_environment
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--paper',action='append');p.add_argument('--timeout',type=int,default=600);p.add_argument('--memory-mb',type=int,default=2048);p.add_argument('--reserve-mb',type=int,default=2048);p.add_argument('--resident-mb',type=int);p.add_argument('--threads',type=int,default=1);a=p.parse_args()
 if a.threads<1:p.error('--threads must be positive')
 if a.resident_mb is not None and (os.name!='nt' or a.resident_mb<64):p.error('--resident-mb needs Windows and at least 64 MiB')
 rows=load(ROOT/'migration/papers.json');results=current_results(load(LOCAL/'results.json',{}));reports=load(ROOT/'migration/axiom-audits.json',{})
 LOCAL.mkdir(parents=True,exist_ok=True)
 env,leanexe=project_environment(a.threads)
 for row in rows:
  if a.paper and row['id'] not in a.paper:continue
  if any(results.get(f[:-5].replace('/','.'),{}).get('status')!='PASS' or results[f[:-5].replace('/','.')].get('source_sha256')!=digest(ROOT/f) for f in row['closure']):
   reports.pop(row['id'],None)
   print(row['id'],'WAITING_FOR_COMPILATION');continue
  free=available_mb()
  launch_budget=min(a.memory_mb,a.resident_mb+512) if a.resident_mb else a.memory_mb
  if free is not None and free<launch_budget+a.reserve_mb:print('RESOURCE_BLOCKED');break
  claims=load(ROOT/row['directory']/'claims.json')['formal_claims']
  if not claims:continue
  modules=sorted({c['module'] for c in claims});names=sorted({c['declaration'] for c in claims})
  if not all(re.fullmatch(r'[A-Za-z_][\w\'.]*',n) for n in modules+names):raise RuntimeError('Unsafe declaration identifier')
  code='\n'.join('import '+m for m in modules)+'\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
  target=LOCAL/(row['id']+'Audit.lean');target.write_text(code,encoding='utf-8');log=LOCAL/(row['id']+'Audit.log')
  command=[leanexe,'-DwarningAsError=true','-j',str(a.threads),'-M',str(a.memory_mb),str(target)]
  status,exitcode,duration=run(command,log,a.timeout,env,a.reserve_mb,a.resident_mb)
  text=log.read_text(encoding='utf-8',errors='replace')
  found={}
  for name,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text):found[name]=[x.strip() for x in axioms.split(',') if x.strip()]
  for name in re.findall(r"'([^']+)' does not depend on any axioms",text):found[name]=[]
  if status=='PASS' and (set(found)!=set(names) or any('sorryAx' in ax for axs in found.values() for ax in axs)):status='FAIL'
  reports[row['id']]={'status':status,'exit_code':exitcode,'duration_seconds':duration,'checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'declarations':found,'nonstandard_axioms':sorted({x for xs in found.values() for x in xs if x not in ['propext','Classical.choice','Quot.sound']}),'audit_source_sha256':digest(target),'log_sha256':digest(log),'module_source_hashes':{f:results[f[:-5].replace('/','.')]['source_sha256'] for f in row['closure']},'environment_hash':environment_hash(),'module_fingerprints':{f:results[f[:-5].replace('/','.')]['fingerprint'] for f in row['closure']},'resources':load(log.with_suffix('.resources.json'),{})}
  reports[row['id']].update(threads=a.threads,memory_mb=a.memory_mb)
  save(ROOT/'migration/axiom-audits.json',reports);print(row['id'],status,flush=True)
 save(ROOT/'migration/axiom-audits.json',reports)
 return 0
if __name__=='__main__':raise SystemExit(main())
