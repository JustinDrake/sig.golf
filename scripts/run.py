"""Adapt the pinned beta verifier's accepted certificate to a Yukon score."""
import json
from pathlib import Path
import subprocess
import sys
import uuid

score_path = Path("scripts/score.json")
score_path.unlink(missing_ok=True)
if sys.platform != "linux":
    raise SystemExit("Official verification requires Linux; the upstream macOS mode is unsandboxed")
command = [sys.executable, "verifier/verify.py", "--local", "submission",
           "--trusted", ".", "--work", f".work/{uuid.uuid4().hex}"]
result = subprocess.run(command, stdout=subprocess.PIPE, text=True)
print(result.stdout, end="")
if result.returncode:
    raise SystemExit(result.returncode)
report = json.loads(result.stdout)
if report["status"] != "verified":
    raise SystemExit("Verifier did not accept the submission")
claim = report["claim"]
size, cycles = claim["S"], claim["C"]
if type(size) is not int or type(cycles) is not int or size <= 0 or cycles < 0:
    raise SystemExit("Invalid verifier metrics")
score = size * cycles
if type(report["score"]) is not int or report["score"] != score or score > 2**53 - 1:
    raise SystemExit("Score is inconsistent or exceeds Yukon's exact integer range")
contract = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
if report["contract_commit"] != contract:
    raise SystemExit("Verifier used a different contract from the repository commit")
metrics = {"signatureBytes": size, "verificationCycles": cycles, "witnessBytes": claim["W"],
           "contractCommit": contract, "verified": True}
temporary = score_path.with_suffix(".tmp")
temporary.write_text(json.dumps({"score": score, "metrics": metrics}) + "\n")
temporary.replace(score_path)
