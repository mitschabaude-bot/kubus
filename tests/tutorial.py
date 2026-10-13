#!/usr/bin/env python3
"""Checks docs/tutorial.md: the `kubus` code blocks form programs (a block starting with
`import` starts a new one), whose output must be the `text` blocks that follow them; the
`kubus-lib` blocks must appear verbatim in lib/."""
import os, re, subprocess, sys, tempfile

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
doc = open(os.path.join(root, "docs", "tutorial.md")).read()
blocks = re.findall(r"^```(\S+)\n(.*?)^```$", doc, re.S | re.M)
programs = []  # [code, expected output]
lib = "".join(open(os.path.join(root, "lib", f)).read() for f in os.listdir(os.path.join(root, "lib")))
fails = 0
for lang, body in blocks:
    if lang == "kubus":
        if not programs or body.startswith("import"):
            programs.append(["", ""])
        programs[-1][0] += body + "\n"
    elif lang == "text":
        programs[-1][1] += body
    elif lang == "kubus-lib":
        if body not in lib:
            print("FAIL tutorial: kubus-lib block not found in lib/:\n" + body); fails += 1
env = dict(os.environ, KUBUS_PATH=os.path.join(root, "lib"))
for k, (code, expected) in enumerate(programs):
    with tempfile.NamedTemporaryFile("w", suffix=".ktt", delete=False) as f:
        f.write(code)
    p = subprocess.run([os.path.join(root, ".lake/build/bin/kubus"), "--selfcheck-main", f.name],
                       capture_output=True, text=True, env=env, timeout=120)
    os.unlink(f.name)
    if p.returncode != 0 or p.stdout != expected:
        print(f"FAIL tutorial program {k + 1}:\n{p.stderr}\n--- got:\n{p.stdout}--- expected:\n{expected}"); fails += 1
sys.exit(1 if fails else 0)
