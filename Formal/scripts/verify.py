"""Build the public Lean sources sequentially, with bounded, resumable receipts.

Uses Python's standard library and the exact Lean/Lake pins in mathlib4_project.
No Erdos path, inherited LEAN_PATH, or original project artifact is used.
"""
from __future__ import annotations
import argparse,ctypes,datetime,hashlib,json,os,signal,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
ENV=ROOT/'mathlib4_project'
LOCAL=ROOT/'.migration-local/verification'

def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as stream:
  for b in iter(lambda:stream.read(1048576),b''):h.update(b)
 return h.hexdigest()
def load(p,default=None):return json.loads(p.read_text(encoding='utf-8')) if p.exists() else default
def save(p,data):
 p.parent.mkdir(parents=True,exist_ok=True);tmp=p.with_suffix(p.suffix+'.tmp')
 tmp.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n',encoding='utf-8');tmp.replace(p)

def environment_hash():
 return hashlib.sha256(''.join(digest(ENV/f) for f in ['lean-toolchain','lakefile.lean','lake-manifest.json']).encode()).hexdigest()

def project_environment(threads=1):
 if threads<1:raise ValueError('Lean thread count must be positive')
 subprocess_env=os.environ.copy()
 for key in ['LEAN_PATH','LEAN_SRC_PATH','LAKE_HOME','LAKE_OVERRIDE_LEAN']:subprocess_env.pop(key,None)
 subprocess_env['LEAN_NUM_THREADS']=str(threads)
 cmd=['lake','env',sys.executable,'-c','import json,os; print(json.dumps(dict(os.environ)))']
 result=subprocess.run(cmd,cwd=ENV,env=subprocess_env,capture_output=True,text=True,timeout=120)
 if result.returncode:raise RuntimeError(result.stderr)
 leanenv=json.loads(result.stdout)
 lean=subprocess.run(['lake','env','lean','--print-prefix'],cwd=ENV,env=subprocess_env,capture_output=True,text=True,check=True,timeout=120).stdout.strip()
 core=(Path(lean)/'lib/lean').resolve()
 for item in leanenv.get('LEAN_PATH','').split(os.pathsep):
  resolved=(Path(item) if Path(item).is_absolute() else ENV/item).resolve()
  if item and not (resolved.is_relative_to(ROOT.resolve()) or resolved==core):raise RuntimeError('External Lean search path rejected: '+item)
 leanenv['LEAN_NUM_THREADS']=str(threads)
 return leanenv,str(Path(lean)/'bin'/('lean.exe' if os.name=='nt' else 'lean'))

def current_results(results):
 """Invalidate receipts when sources, transitive inputs or artifacts change."""
 modules={m['module']:m for m in load(ROOT/'migration/modules.json')}
 config=environment_hash();fingerprints={};active=set()
 def visit(name):
  if name in fingerprints:return fingerprints[name]
  if name in active:raise RuntimeError('Local import cycle: '+name)
  active.add(name);m=modules[name];source=ROOT/(name.replace('.','/')+'.lean')
  actual=digest(source)
  if actual!=m['sha256']:raise RuntimeError('Source inventory is stale: '+name)
  deps=[i for i in m['imports'] if i in modules]
  fingerprint=hashlib.sha256((actual+config+''.join(visit(i) for i in deps)).encode()).hexdigest()
  fingerprints[name]=fingerprint;active.remove(name)
  old=results.get(name,{})
  if old.get('status')=='PASS':
   artifact=ENV/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean')
   if old.get('fingerprint')!=fingerprint or not artifact.is_file() or digest(artifact)!=old.get('artifact_sha256') or any(results.get(i,{}).get('status')!='PASS' for i in deps):
    results[name]={**old,'status':'STALE'}
  return fingerprint
 # Only successful receipts can be reused. Validate their transitive inputs;
 # untouched modules are hashed immediately before their own compilation.
 # This avoids reading the entire certificate collection for a one-module pilot.
 for name,previous in list(results.items()):
  if name in modules and previous.get('status')=='PASS':visit(name)
 return {name:value for name,value in results.items() if name in modules}
def available_mb(field='available'):
 if os.name=='nt':
  class Memory(ctypes.Structure):
   _fields_=[('length',ctypes.c_ulong),('load',ctypes.c_ulong)]+[(n,ctypes.c_ulonglong) for n in ['total','available','page_total','page_available','virtual_total','virtual_available','extended']]
  m=Memory();m.length=ctypes.sizeof(m);ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m));return getattr(m,field)/1048576
 if field!='available':return None
 try:
  for line in Path('/proc/meminfo').read_text().splitlines():
   if line.startswith('MemAvailable:'):return int(line.split()[1])/1024
 except OSError:pass
 return None
def terminate(p):
 if p.poll() is not None:return
 if os.name=='nt':subprocess.run(['taskkill','/PID',str(p.pid),'/T','/F'],capture_output=True)
 else:os.killpg(p.pid,signal.SIGKILL)
 p.wait()
def run(command,log,timeout,env,reserve,resident_mb=None):
 start=time.monotonic();status=None;minimum_free=None;minimum_commit=None;peak_working=0;reserve_reason=None
 with log.open('w',encoding='utf-8') as out:
  p=subprocess.Popen(command,cwd=ENV,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=os.name!='nt')
  try:
   if resident_mb is not None:
    if os.name!='nt':raise RuntimeError('--resident-mb currently requires Windows')
    kernel=ctypes.WinDLL('kernel32',use_last_error=True)
    handle=ctypes.c_void_p(int(p._handle))
    # Hard maximum; permit the minimum to shrink. Only this owned process changes.
    if not kernel.SetProcessWorkingSetSizeEx(handle,ctypes.c_size_t(1048576),ctypes.c_size_t(resident_mb*1048576),ctypes.c_ulong(6)):
     raise ctypes.WinError(ctypes.get_last_error())
    minimum=ctypes.c_size_t();maximum=ctypes.c_size_t();flags=ctypes.c_ulong()
    if not kernel.GetProcessWorkingSetSizeEx(handle,ctypes.byref(minimum),ctypes.byref(maximum),ctypes.byref(flags)):
     raise ctypes.WinError(ctypes.get_last_error())
    if not flags.value&4 or maximum.value>resident_mb*1048576:raise RuntimeError('Windows did not confirm the resident-memory cap')
   while p.poll() is None:
    if time.monotonic()-start>timeout:status='TIMEOUT';terminate(p);break
    free=available_mb()
    if free is not None:minimum_free=free if minimum_free is None else min(minimum_free,free)
    if os.name=='nt':
     class Counters(ctypes.Structure):
      _fields_=[('cb',ctypes.c_ulong),('faults',ctypes.c_ulong)]+[(n,ctypes.c_size_t) for n in ['peak_working','working','peak_paged','paged','peak_nonpaged','nonpaged','pagefile','peak_pagefile','private']]
     counters=Counters();counters.cb=ctypes.sizeof(counters)
     if ctypes.windll.psapi.GetProcessMemoryInfo(ctypes.c_void_p(int(p._handle)),ctypes.byref(counters),ctypes.sizeof(counters)):
      peak_working=max(peak_working,counters.peak_working/1048576)
    commit_free=available_mb('page_available')
    if commit_free is not None:minimum_commit=commit_free if minimum_commit is None else min(minimum_commit,commit_free)
    if free is not None and free<reserve:status='RESOURCE_BLOCKED';reserve_reason='PHYSICAL_MEMORY_RESERVE';terminate(p);break
    if commit_free is not None and commit_free<reserve:status='RESOURCE_BLOCKED';reserve_reason='COMMIT_MEMORY_RESERVE';terminate(p);break
    time.sleep(.5)
  except BaseException:terminate(p);raise
 reason=reserve_reason or status
 text=log.read_text(encoding='utf-8',errors='replace')
 if status is None and p.returncode and 'excessive memory consumption' in text:
  status='RESOURCE_BLOCKED';reason='LEAN_MANAGED_MEMORY_LIMIT'
 save(log.with_suffix('.resources.json'),{'minimum_available_mb':round(minimum_free,1) if minimum_free is not None else None,'minimum_commit_available_mb':round(minimum_commit,1) if minimum_commit is not None else None,'peak_process_working_set_mb':round(peak_working,1) if os.name=='nt' else None,'reserve_mb':reserve,'resident_limit_mb':resident_mb,'stop_reason':reason})
 return status or ('PASS' if p.returncode==0 else 'FAIL'),p.returncode,round(time.monotonic()-start,3)
def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--paper',action='append',help='P001..P060; repeatable')
 parser.add_argument('--module',action='append',help='Exact module name; repeatable')
 parser.add_argument('--max-modules',type=int,default=40)
 parser.add_argument('--max-seconds',type=int,default=3600)
 parser.add_argument('--timeout',type=int,default=600)
 parser.add_argument('--memory-mb',type=int,default=2048)
 parser.add_argument('--reserve-mb',type=int,default=2048)
 parser.add_argument('--resident-mb',type=int,help='Windows hard working-set cap for the owned Lean process; may increase paging')
 parser.add_argument('--list',action='store_true')
 parser.add_argument('--retry-failed',action='store_true')
 parser.add_argument('--threads',type=int,default=1,help='Lean worker threads inside the single bounded compiler process')
 args=parser.parse_args()
 if args.threads<1:parser.error('--threads must be positive')
 if args.resident_mb is not None and (os.name!='nt' or args.resident_mb<64):parser.error('--resident-mb needs Windows and at least 64 MiB')
 modules=load(ROOT/'migration/modules.json');byname={m['module']:m for m in modules}
 rows=load(ROOT/'migration/papers.json');selected=set(byname)
 if args.paper:
  valid={r['id']:r for r in rows}
  unknown=set(args.paper)-valid.keys()
  if unknown:parser.error('Unknown paper: '+','.join(unknown))
  selected={f[:-5].replace('/','.') for pid in args.paper for f in valid[pid]['closure']}
 if args.module:
  unknown=set(args.module)-byname.keys()
  if unknown:parser.error('Unknown module: '+','.join(unknown))
  selected=set(args.module)
 ordered=[];seen=set();active=set()
 def visit(m):
  if m in seen:return
  if m in active:raise RuntimeError('Local import cycle: '+m)
  active.add(m)
  for imp in byname[m]['imports']:
   if imp in byname:visit(imp)
  active.remove(m);seen.add(m);ordered.append(m)
 for m in sorted(selected):visit(m)
 if args.list:
  print(json.dumps({'module_count':len(ordered),'modules':ordered},indent=2));return 0
 LOCAL.mkdir(parents=True,exist_ok=True)
 leanenv,leanexe=project_environment(args.threads)
 config_hash=environment_hash()
 results=current_results(load(LOCAL/'results.json',{}))
 fingerprints={};outputs=ENV/'.lake/build/lib/lean';outputs.mkdir(parents=True,exist_ok=True)
 started=time.monotonic();ran=0;blocked=[]
 for index,name in enumerate(ordered):
  source=ROOT/(name.replace('.','/')+'.lean')
  actual=digest(source)
  if actual!=byname[name]['sha256']:raise RuntimeError('Source inventory is stale: '+name)
  fingerprint=hashlib.sha256((actual+config_hash+''.join(fingerprints.get(i,'') for i in byname[name]['imports'] if i in byname)).encode()).hexdigest();fingerprints[name]=fingerprint
  output=outputs/(name.replace('.','/')+'.olean');previous=results.get(name,{})
  if previous.get('status')=='PASS' and previous.get('fingerprint')==fingerprint and output.exists() and digest(output)==previous.get('artifact_sha256'):continue
  if previous.get('status') in ['FAIL','TIMEOUT','RESOURCE_BLOCKED'] and previous.get('fingerprint')==fingerprint and not args.retry_failed:blocked.append(name);continue
  if any(results.get(i,{}).get('status')!='PASS' or results[i].get('fingerprint')!=fingerprints.get(i) for i in byname[name]['imports'] if i in byname):blocked.append(name);continue
  if ran>=args.max_modules or time.monotonic()-started>=args.max_seconds:break
  free=available_mb()
  # Measured capped pilots support a smaller physical launch allowance, with
  # 512 MiB extra headroom for effects outside the owned process working set.
  launch_budget=min(args.memory_mb,args.resident_mb+512) if args.resident_mb else args.memory_mb
  if free is not None and free<args.reserve_mb+launch_budget:
   print('RESOURCE_BLOCKED: %.0f MiB available; need %d before next module.'%(free,args.reserve_mb+launch_budget),flush=True);break
  output.parent.mkdir(parents=True,exist_ok=True)
  log=LOCAL/(name+'.log')
  command=[leanexe,'-DwarningAsError=true','-j',str(args.threads),'-M',str(args.memory_mb),'-R',str(ROOT),'-o',str(output),str(source)]
  print('[%d/%d] %s'%(index+1,len(ordered),name),flush=True)
  status,code,duration=run(command,log,min(args.timeout,max(1,args.max_seconds-int(time.monotonic()-started))),leanenv,args.reserve_mb,args.resident_mb)
  text=log.read_text(encoding='utf-8',errors='replace')
  if status=='PASS' and ('warning:' in text or 'error:' in text):status='FAIL'
  results[name]={'status':status,'exit_code':code,'fingerprint':fingerprint,'source_sha256':actual,'duration_seconds':duration,'log_sha256':digest(log),'artifact_sha256':digest(output) if status=='PASS' and output.exists() else None,'checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'memory_mb':args.memory_mb,'threads':args.threads}
  results[name]['resources']=load(log.with_suffix('.resources.json'),{})
  save(LOCAL/'results.json',results);ran+=1
  print(status,duration,'seconds',flush=True)
  if status=='RESOURCE_BLOCKED':break
 # Public evidence excludes machine paths and private process details.
 public={'kind':'DESTINATION_COMPILATION','environment_hash':config_hash,'results':results,'axiom_audit':'PENDING; compilation alone does not audit advertised declarations','completed_modules':sum(x.get('status')=='PASS' for x in results.values()),'production_modules':len(modules)}
 save(LOCAL/'results.json',results)
 save(ROOT/'migration/verification.json',public)
 print(json.dumps({'invocations_this_run':ran,'passed':public['completed_modules'],'total':len(modules),'dependency_blocked':len(blocked)}),flush=True)
 return 0
if __name__=='__main__':raise SystemExit(main())
