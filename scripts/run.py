"""Adapt the pinned beta verifier's accepted certificate to a Yukon score."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import uuid

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--reverify', action='store_true')
parser.add_argument('--fresh-kernel', action='store_true')
parser.add_argument('--no-cache', action='store_true')
parser.add_argument('--worker', type=Path)
parser.add_argument('--cache-dir', type=Path)
parser.add_argument('--preview', action='store_true')
parser.parse_args()

score_path = Path("scripts/score.json")
score_path.unlink(missing_ok=True)
command = [sys.executable, "verifier/verify.py", "--local", "submission",
           "--trusted", ".", "--work", f".work/{uuid.uuid4().hex}", *sys.argv[1:]]
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
            "contractCommit": contract, "verified": True, "verificationMode": report["mode"],
            "sourceDigest": report["source_digest"], "contextDigest": report["context_digest"],
            "certificateDigest": report["certificate_digest"], "cacheHit": report["cache_hit"],
            "verificationSeconds": report["timings_seconds"]["total"]}
temporary = score_path.with_suffix(".tmp")
temporary.write_text(json.dumps({"score": score, "metrics": metrics}) + "\n")
temporary.replace(score_path)
