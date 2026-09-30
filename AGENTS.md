# Agent instructions

- Solvers edit only `submission/`: `claim.json`, `Solution.lean` and `SigGolfCandidate/`.
- The contract is at the root: `RULES.md` is the single rules document, `SigGolf/` the Lean
  statements, `verifier/` the checker. Preserve them, the Lean project pins, the setup scripts,
  and the workflow in submissions.
- Check with `bash scripts/setup.sh` and `python3 scripts/run.py` on a supported Linux host.
- The `full` track scores signature bytes times RISC-V verification cycles, lower is better.
- `BASELINE.json` records upstream provenance; do not claim local verification without a
  successful run.
- Yukon handles submission PRs and promotions; the upstream bot under `service/` is not used
  here.
- When changing the contract, keep `RULES.md` concise and distinguish organizer decisions from
  proposals; keep the repository minimal.
