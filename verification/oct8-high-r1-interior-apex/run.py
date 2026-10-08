from pathlib import Path
import hashlib
import json
import os
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
MODULE = "Jsp000404.ActualHighR1InteriorApex"
SOURCE = ROOT / "Jsp000404/ActualHighR1InteriorApex.lean"
HERE = Path(__file__).resolve().parent

kind, attempt_text = sys.argv[1:]
assert kind in ("strict0", "normal")
attempt = int(attempt_text)
assert 1 <= attempt <= 3
base = HERE / f"{kind}-attempt{attempt}"
log = Path(str(base) + ".stdout.txt")
snapshot = Path(str(base) + ".source.lean")
assert not log.exists() and not snapshot.exists(), "Preserve previous exact evidence"
data = SOURCE.read_bytes()
source_hash = hashlib.sha256(data).hexdigest()
if kind == "strict0" and attempt == 1:
    assert source_hash == "5e7440e8ec8f5428627e95e220b9914a412f509c3861151f3e3aa4c7e9050a09"
parents = json.loads((HERE / "parents-current-sha256.json").read_text())
for name, expected in parents.items():
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected, "Frozen parent changed: " + name
active = []
for line in subprocess.check_output(["ps", "-axo", "pid=,comm="], text=True).splitlines():
    parts = line.strip().split(None, 1)
    if len(parts) == 2 and Path(parts[1]).name in ("lean", "lake"):
        active.append(line.strip())
if active:
    print("PREFLIGHT_REFUSED " + json.dumps(active), flush=True)
    sys.exit(2)
snapshot.write_bytes(data)
command = (["lake", "env", "lean", "--trust=0", "-M8192", str(SOURCE.relative_to(ROOT))]
           if kind == "strict0" else ["lake", "build", MODULE])
start = time.monotonic()
peak = 0
reason = None
with log.open("wb") as output:
    process = subprocess.Popen(["/usr/bin/time", "-l", *command], cwd=ROOT,
                               stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
    print("START " + json.dumps({"pid": process.pid, "kind": kind, "attempt": attempt,
                                "source_sha256": source_hash, "stdout": str(log.relative_to(ROOT))}), flush=True)
    while process.poll() is None:
        rows = subprocess.check_output(["ps", "-axo", "pgid=,rss="], text=True).splitlines()
        rss = sum(int(parts[1]) * 1024 for line in rows
                  if len(parts := line.split()) == 2 and int(parts[0]) == process.pid)
        peak = max(peak, rss)
        if rss > 8 * 1024**3:
            reason = "rss_8GiB"
        if time.monotonic() - start > 180:
            reason = "wall_180s"
        if reason:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
            break
        time.sleep(0.25)
    result = {"module": MODULE, "kind": kind, "attempt": attempt, "command": command,
              "exit_code": process.wait(), "guard_reason": reason,
              "elapsed_seconds": round(time.monotonic() - start, 3),
              "peak_process_group_rss_bytes": peak, "source_sha256": source_hash,
              "snapshot": str(snapshot.relative_to(ROOT)), "stdout": str(log.relative_to(ROOT)),
              "source_unchanged": SOURCE.read_bytes() == data}
    output.write(("\nGUARD_RESULT " + json.dumps(result) + "\n").encode())
print(json.dumps(result), flush=True)
print(log.read_text()[-12000:], flush=True)
