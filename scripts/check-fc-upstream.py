#!/usr/bin/env python3
"""Check the single submission file with a real FC checkout and its pinned Lean/Mathlib.

The upstream checkout and cached dependency builds are read-only. Only the required
FC modules are compiled, in a small automatically removed temporary directory.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from graphlib import TopologicalSorter
import argparse, hashlib, json, os, re, subprocess, tempfile, time

ROOT = Path(__file__).resolve().parents[1]

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--fc-source', type=Path, required=True)
    ap.add_argument('--dependency-build', type=Path, required=True)
    ap.add_argument('--record', action='store_true')
    args = ap.parse_args()
    fc, deps = args.fc_source.resolve(), args.dependency_build.resolve()
    toolchain = (fc/'lean-toolchain').read_text().strip()
    lean = subprocess.check_output(['elan', 'which', 'lean'], env=dict(os.environ, ELAN_TOOLCHAIN=toolchain), text=True).strip()
    pins = {p['name']:p['rev'] for p in json.loads((fc/'lake-manifest.json').read_text())['packages']}
    dep_pins = {p['name']:p['rev'] for p in json.loads((deps/'lake-manifest.json').read_text())['packages']}
    assert all(dep_pins.get(n)==v for n,v in pins.items()), 'FC dependency pins differ'
    paths = [deps/'.lake/packages'/n/'.lake/build/lib/lean' for n in pins]
    paths = [p for p in paths if p.exists()]
    assert (deps/'.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean').exists(), 'Mathlib build missing'
    graph = {}
    def visit(name):
        if name in graph: return
        p = fc/(name.replace('.', '/')+'.lean')
        imports = [n.replace('«','').replace('»','') for n in
            re.findall(r'(?m)^(?:public )?(?:meta )?import(?: all)? ([\w.«»]+)', p.read_text())]
        children = [n for n in imports if (fc/(n.replace('.', '/')+'.lean')).exists()]
        graph[name] = children
        for child in children: visit(child)
    visit('FormalConjecturesUtil')
    config = (fc/'lakefile.toml').read_text()
    # Match FC's Lake options (in particular the Unicode output used by guard_msgs).
    def options(section):
        # FC uses scalar bool/string values here; reject unsupported assignments.
        result=[]
        for line in section.splitlines():
            if not line.strip() or line.lstrip().startswith('#'): continue
            key,value=line.split('=',1)
            result.append('-D'+key.strip()+'='+str(json.loads(value)).lower())
        return result
    common_options = options(re.search(r'(?ms)^\[leanOptions\]\n(.*?)(?=^\[|\Z)',config)[1])
    problem_table = config.split('name = "FormalConjectures"',1)[1]
    problem_options = options(re.search(r'(?ms)^\[lean_lib.leanOptions\]\n(.*?)(?=^\[|\Z)',problem_table)[1])
    problem_options = [v for v in problem_options if not v.startswith('-Dwarn.sorry=')]
    receipt = {'kind':'actual-upstream-fc-check', 'lean_toolchain':toolchain,
      'upstream_commit':subprocess.check_output(['git','-C',str(fc),'rev-parse','HEAD'],text=True).strip(),
      'dependency_pins':pins, 'upstream_modules':len(graph), 'clean_mathlib_build':False,
      'lean_options':common_options, 'problem_options':problem_options,
      'inputs_sha256':{n:sha(ROOT/n) for n in ['FClikelean/ReversibleFinslerSpheres.lean',
        'verification/FCStatementReadback.lean','scripts/check-fc-upstream.py']},
      'upstream_sources_sha256':{n:sha(fc/(n.replace('.','/')+'.lean')) for n in graph}, 'checks':[]}
    logs=[]
    started=time.monotonic()
    with tempfile.TemporaryDirectory(prefix='finsler-fc-upstream-') as td:
        work=Path(td)
        env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[work]+paths)),LEAN_NUM_THREADS='2')
        def compile_file(name, source, root, output=None):
            cmd=[lean,'-M8192','-j2','-DElab.async=false',*common_options,'--root='+str(root)]
            if name == 'FClikelean/ReversibleFinslerSpheres.lean':
                cmd += problem_options
            if output:
                target=work/(output.replace('.','/')+'.olean')
                target.parent.mkdir(parents=True,exist_ok=True)
                cmd+=['-o',str(target)]
            cmd.append(str(source))
            t=time.monotonic()
            try:
                p=subprocess.run(cmd,cwd=work,env=env,text=True,stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,timeout=180)
                code,out=p.returncode,p.stdout
            except subprocess.TimeoutExpired as e:
                code,out=124,e.stdout or b''
                if isinstance(out,bytes):out=out.decode(errors='replace')
            return {'file':name,'exit_code':code,'seconds':round(time.monotonic()-t,3)},out
        sorter=TopologicalSorter(graph)
        sorter.prepare()
        ready=list(sorter.get_ready())
        count=0
        with ThreadPoolExecutor(max_workers=2) as pool:
            active={}
            while ready or active:
                while ready and len(active)<2:
                    n=ready.pop()
                    active[pool.submit(compile_file,n,fc/(n.replace('.','/')+'.lean'),fc,n)]=n
                done,_=wait(active,return_when=FIRST_COMPLETED)
                for fut in done:
                    n=active.pop(fut)
                    result,out=fut.result()
                    receipt['checks'].append(result)
                    logs.append(n+'\n'+out)
                    if result['exit_code']:
                        print('FAILED',n,out,flush=True)
                        raise RuntimeError('Upstream module failed: '+n)
                    count+=1
                    if count%10==0: print(f'FC support: {count}/{len(graph)}',flush=True)
                    sorter.done(n)
                ready.extend(sorter.get_ready())
        for name,root,module in [
          ('FClikelean/ReversibleFinslerSpheres.lean','FClikelean','ReversibleFinslerSpheres'),
          ('verification/FCStatementReadback.lean','verification',None)]:
            result,out=compile_file(name,ROOT/name,ROOT/root,module)
            receipt['checks'].append(result)
            logs.append(name+'\n'+out)
            print(name, result, out, flush=True)
            assert result['exit_code']==0, name
            warnings=len(re.findall(r'declaration uses [`\']sorry[`\']',out))
            assert warnings==(4 if module else 0), 'Unexpected proof placeholders'
        receipt['temporary_build_bytes']=sum(p.stat().st_size for p in work.rglob('*') if p.is_file())
    assert all(sha(ROOT/n)==h for n,h in receipt['inputs_sha256'].items()), 'Sources changed during check'
    receipt.update(status='pass',temporary_build_removed=not Path(td).exists(),seconds=round(time.monotonic()-started,3))
    if args.record:
        dest=ROOT/'verification/local'
        dest.mkdir(exist_ok=True)
        (dest/'fc-upstream.log').write_text('\n'.join(logs))
        receipt['log_sha256']=sha(dest/'fc-upstream.log')
        (dest/'fc-upstream-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS: actual FC import, four statement types and metadata; temporary build removed.',flush=True)

if __name__=='__main__': main()
