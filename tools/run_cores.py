import subprocess, sys, os
profs = ["(('ge',3),('ge',3))", "(('ge',3),1)", "(('ge',3),2)", "(0,('ge',3))", "(1,('ge',3))", "(2,('ge',3))", "(('ge',3),0)"]
targets = sys.argv[1:]
procs = []
for t in targets:
    for p in profs:
        procs.append((t, p, subprocess.Popen([sys.executable, "-u", "vd_core.py", p, t], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)))
for t, p, pr in procs:
    out, _ = pr.communicate(timeout=1800)
    print(out.strip()); print("-" * 40, flush=True)
