from pathlib import Path
import subprocess, sys, json, time, resource, os
v=Path(__file__).resolve().parent
binpath='/Users/jenwin/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin'
label=sys.argv[1]; args=sys.argv[2:]
envargs=['HOME='+str(v/'home'),'TMPDIR='+str(v/'tmp'),'PATH='+binpath+':/usr/bin:/bin:/usr/sbin:/sbin','LANG=en_US.UTF-8','LEAN_NUM_THREADS=2']
cmd=['/usr/bin/sandbox-exec','-f',str(v/'audit/isolation.sb'),'/usr/bin/env','-i',*envargs,*args]
def limits():
    resource.setrlimit(resource.RLIMIT_CPU,(1800,1800))
    resource.setrlimit(resource.RLIMIT_FSIZE,(2*1024**3,2*1024**3))
    resource.setrlimit(resource.RLIMIT_NOFILE,(1024,1024))
start=time.time()
with (v/'logs'/f'{label}.log').open('wb') as f:
    p=subprocess.run(cmd,cwd=v/'source',stdout=f,stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL,preexec_fn=limits)
r={'label':label,'command':cmd,'cwd':str(v/'source'),'exit_code':p.returncode,'seconds':round(time.time()-start,3)}
with (v/'execution.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
print(json.dumps(r));sys.exit(p.returncode)
