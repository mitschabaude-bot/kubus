#!/usr/bin/env python3
"""Smoke test of `kubus --lsp`: diagnostics with ranges, #eval output, hole goals, hover."""
import json, os, subprocess, sys

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
text = """import circle

def f (x : S1) : Path S1 x x := refl x
def g (p : Path S1 base base) : Int := winding (trans p ?)
def bad : Path S1 base base := refl (pos zero)
#eval winding (trans loopP loopP)
"""
uri = "file://" + os.path.join(root, "tests", "lsp_doc.ktt")

def frame(o):
    b = json.dumps(o).encode()
    return b"Content-Length: %d\r\n\r\n" % len(b) + b

msgs = [{"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}},
        {"jsonrpc": "2.0", "method": "initialized", "params": {}},
        {"jsonrpc": "2.0", "method": "textDocument/didOpen",
         "params": {"textDocument": {"uri": uri, "languageId": "kubus", "version": 1, "text": text}}},
        {"jsonrpc": "2.0", "id": 2, "method": "textDocument/hover",
         "params": {"textDocument": {"uri": uri}, "position": {"line": 2, "character": 37}}},
        {"jsonrpc": "2.0", "id": 4, "method": "textDocument/hover",
         "params": {"textDocument": {"uri": uri}, "position": {"line": 2, "character": 4}}},
        {"jsonrpc": "2.0", "id": 3, "method": "shutdown"},
        {"jsonrpc": "2.0", "method": "exit"}]
env = dict(os.environ, KUBUS_PATH=os.path.join(root, "lib"))
p = subprocess.run([os.path.join(root, ".lake/build/bin/kubus"), "--lsp"], input=b"".join(map(frame, msgs)),
                   capture_output=True, env=env, timeout=60)
out, replies = p.stdout, []
while out:
    head, _, rest = out.partition(b"\r\n\r\n")
    n = int(head.split(b":")[1])
    replies.append(json.loads(rest[:n]))
    out = rest[n:]
diags = next(r for r in replies if r.get("method") == "textDocument/publishDiagnostics")["params"]["diagnostics"]
hover = next(r for r in replies if r.get("id") == 2)["result"]["contents"]["value"]
hover4 = (next(r for r in replies if r.get("id") == 4)["result"] or {}).get("contents", {}).get("value", "")
checks = [
    ("type error with its range", any(d["severity"] == 1 and "type mismatch" in d["message"]
        and d["range"] == {"start": {"line": 4, "character": 31}, "end": {"line": 4, "character": 46}} for d in diags)),
    ("goal of the hole", any(d["severity"] == 3 and d["message"].startswith("goal: Path S1 base base") for d in diags)),
    ("#eval output", any(d["severity"] == 3 and d["message"].startswith("pos (suc (suc zero))") for d in diags)),
    ("hover", "x : S1" in hover),
    ("certified by the kernel", "certified by the kernel" in hover4),
    ("no kernel warning for a definition with a hole", not any("kernel" in d["message"] for d in diags)),
]
failed = [name for name, ok in checks if not ok]
if failed:
    print("FAIL lsp:", ", ".join(failed)); print(json.dumps(replies, indent=1)[:3000]); sys.exit(1)
