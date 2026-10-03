# sig.golf on Yukon

Optimize a stateless hash-based signature scheme under the [beta rules](RULES.md).
The single `full` track minimizes **signature bytes × RISC-V verification cycles**.
Yukon promotions are manual.

## Contract

The contract lives in this repository: `RULES.md` states the rules, `SigGolf/` holds the
Lean statements a certificate proves, `verifier/` checks a submission, and `lakefile.lean`,
`lake-manifest.json`, and `lean-toolchain` pin the Lean project. The contract commit is the
repository commit. The bot under `service/` and the website under `site/` are the upstream
sig.golf deployment and are not used by Yukon.

The proposed baseline is the **6,404 bytes × 11,573 cycles = 74,113,492** SPHINCS+
variant from [upstream PR #34](https://github.com/leanEthereum/sig.golf-submissions/pull/34),
using its [PR #35 cache-size port](https://github.com/leanEthereum/sig.golf-submissions/pull/35)
with a 131,072-byte cache. `BASELINE.json` records the exact source revision. Upstream
accepted it under an earlier contract; this repository's vendored contract requires
fresh verification.

## Develop and submit

Only `submission/` is editable: `claim.json`, `Solution.lean`, the
`SigGolfCandidate/` Lean modules, and an optional bounded `certificate/` bundle.
Source mode builds the frozen candidate under isolation. Certificate mode skips candidate
code execution and kernel-checks declarative proofs bound to all four literal program images.
Both preserve the contract's statement, primitive, and axiom checks. Read `RULES.md` for
the exact model and [`verifier/README.md`](verifier/README.md) for preparation, trust boundaries,
local reuse, and explicit reverification controls.

From the repository root on Linux:

```sh
bash scripts/setup.sh
python3 scripts/run.py
```

Setup installs elan through a pinned installer, selects the contract's Lean toolchain,
builds the verifier tools and trusted `SigGolf` library, and checks Linux prerequisites.
Go 1.24+, Landlock and user systemd with the verifier's required namespace and resource
isolation must be available. The verifier checks isolation before compiling a candidate.
Unsupported hosts fail; there is no unsandboxed scoring fallback. A certificate-only
`python3 verifier/verify.py --local submission --preview` is available for non-scoring local
development on other hosts. It never runs candidate source or publishes acceptance records.

After Yukon import, use `yukon setup --track full`, `yukon run --track full` and
`yukon submit --track full`. `yukon switch full` changes the selected track without
changing Git branches or files. CI evaluates the dispatched checkout; local runs
include working-tree edits. Failed verification emits no score. The wrapper preserves
exact integer scores and rejects any value beyond Yukon's safe integer range.

`python3 scripts/run.py --reverify` bypasses certificate exact-result reuse. Source-only
submissions always rebuild/export. Add `--fresh-kernel` to
force replay from an empty environment. Changed source, certificate, images, claim, contract,
dependencies, checker, or tool identity invalidates exact reuse even under an unchanged Git HEAD.

## Workflow and caches

The manual `benchmark.yml` workflow uses `blacksmith-16vcpu-ubuntu-2404` (64 GB RAM).
Because the Blacksmith host lacks Landlock, `scripts/blacksmith.sh` boots a checksum-pinned
Ubuntu 26.04 KVM guest with 12 vCPUs and 48 GiB RAM. The verifier runs as an unprivileged
user under `/srv`, with Landlock and the upstream systemd isolation checks intact.
The workflow selects four CPU-affined logical CPUs and a 40 GiB limit, with four Lake task
workers and one compiler thread. Local defaults remain two CPUs and 24 GiB. Explicit resource
profiles validate host and guest headroom. The job allows five hours around the verifier's
four-hour overall deadline. The VM is stopped
on success or failure, and verifier logs and the guest console are retained as artifacts.

The guest's elan/toolchains, the complete `.lake` dependency/build workspace and
verifier tools are cached together by contract commit and bootstrap-script hashes.
Only the default branch saves shared caches, before candidate verification. Candidate outputs
are never promoted into this shared trusted cache. Restored tools still run upstream setup
checks. A separate private, host-owned exact acceptance cache reuses only identical validated
requests; uploader-supplied cache records are never accepted. An opt-in long-lived Linux checker
can reuse an immutable, independently kernel-checked dependency base, with full declaration
equality and fresh fallback. CI's ephemeral VM does not persist that worker across Yukon jobs.
Per-stage timing and resource telemetry are retained as artifacts.

Yukon owns submission PRs and promotions. Do not enable the original upstream record
publisher on this repository. `records.json` is not updated by Yukon.

## Verifier tests

```sh
bash scripts/setup.sh --tools-only
bash scripts/test-verifier.sh
```

The suite includes corrupted proof/image inputs, prohibited axioms, invalid inductives and
recursors, cache poisoning attempts, and fresh-versus-reused kernel checks. Python supervisor
tests use mocks for isolation; native fixtures test the real pinned kernel. Neither is a claim
that a full competition submission passed the supported Linux runner.

## License

See `LICENSE` and `THIRD_PARTY_NOTICES.md`.
