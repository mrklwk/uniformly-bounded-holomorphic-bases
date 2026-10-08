#!/usr/bin/env python3
"""Offline, project-only fresh-object verification using an already installed pinned dependency cache."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys,time
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--lean',required=True,type=Path)
p.add_argument('--packages',required=True,type=Path)
p.add_argument('--output',required=True,type=Path)
a=p.parse_args();root=Path(__file__).resolve().parents[1]
lean=a.lean.resolve();packages=a.packages.resolve();out=a.output.resolve()
if out==root or root in out.parents: p.error('Use an output directory outside the source repository.')
lib=out/'objects';logs=out/'logs';lib.mkdir(parents=True,exist_ok=True);logs.mkdir(parents=True,exist_ok=True)
if list(lib.rglob('*.olean')): p.error('Output objects must be empty for a fresh build; choose a new output directory.')
version=subprocess.check_output([str(lean),'--version'],text=True).strip()
expected=(root/'lean-toolchain').read_text().strip().split(':')[-1].removeprefix('v')
if not re.search(r'version '+re.escape(expected)+r'[, )]',version): p.error('Installed Lean does not match lean-toolchain.')
manifest=json.loads((root/'lake-manifest.json').read_text())
deps=[];search=[str(lib)]
for dep in manifest['packages']:
 d=packages/dep['name']
 rev=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip()
 if rev!=dep['rev']: p.error('Dependency revision mismatch: '+dep['name'])
 dirty=subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],text=True)
 if dirty: p.error('Tracked dependency changes: '+dep['name'])
 cache=d/'.lake/build/lib/lean'
 if dep['name']=='mathlib' and not cache.is_dir(): p.error('Missing installed mathlib objects.')
 search.append(str(cache));deps.append({'name':dep['name'],'revision':rev,'tracked_clean':True,'objects_available':cache.is_dir()})
env=dict(os.environ,LEAN_PATH=os.pathsep.join(search),PATH=str(lean.parent)+os.pathsep+os.environ.get('PATH',''))
sources={'.'.join(f.relative_to(root).with_suffix('').parts):f for f in root.rglob('*.lean') if '.lake' not in f.parts}
order=[];active=set();done=set()
def visit(m):
 if m in done or m not in sources:return
 if m in active:raise RuntimeError('Cyclic project import: '+m)
 active.add(m)
 for n in re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)',sources[m].read_text(),re.M):visit(n)
 active.remove(m);done.add(m);order.append(m)
for m in sorted(sources):visit(m)
env['BOURGAIN_AUDIT_OUTPUT']=str(out/'logical-closure.txt')
records=[]
meta={'toolchain':version,'dependencies':deps,'sources':{str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sources.values()},'build':records}
for m in order:
 f=sources[m];rel=f.relative_to(root);obj=lib/rel.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 # The single Challenge placeholder is a statement of record, never a proof dependency.
 cmd=[str(lean),'-DwarningAsError='+('false' if m=='Challenge' else 'true'),'-o',str(obj),str(rel)]
 start=time.monotonic()
 with (logs/(m+'.log')).open('w') as log:r=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
 records.append({'module':m,'command':cmd,'exit_code':r.returncode,'seconds':round(time.monotonic()-start,3)})
 (out/'verification.json').write_text(json.dumps(meta,indent=2)+'\n')
 print(m,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
 if m=='Challenge':
  warning=(logs/(m+'.log')).read_text()
  if warning.count('warning:')!=1 or 'warning: declaration uses `sorry`' not in warning:
   raise RuntimeError('Expected exactly one deliberate Challenge placeholder warning.')
for rel,h in meta['sources'].items():
 if hashlib.sha256((root/rel).read_bytes()).hexdigest()!=h:raise RuntimeError('Source changed during build: '+rel)
(out/'lean-path.txt').write_text(os.pathsep.join(search)+'\n')
reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(logs/'BourgainBasis.Audit.log').read_text())
if len(reports)!=364:raise RuntimeError('Expected 364 production axiom reports.')
for name,axioms in reports:
 if {x.strip() for x in axioms.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:
  raise RuntimeError('Unexpected axioms: '+name)
print('PROJECT-ONLY FRESH BUILD PASS:',len(records),'modules; pinned cached dependencies; 364 standard-axiom reports; source hashes unchanged.',flush=True)
