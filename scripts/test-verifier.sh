#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
if [[ ! -f "$ROOT/verifier/CertificateCheck.lean" || ! -f "$ROOT/verifier/tests/CertificateTests.lean" ]]; then
  printf '%s\n' 'test-verifier: cannot locate the verifier checkout' >&2
  exit 1
fi

python_only=false
case "${1:-}" in
  --python-only) python_only=true; shift ;;
  --help) printf '%s\n' 'Usage: scripts/test-verifier.sh [--python-only]'; exit 0 ;;
  '') ;;
  *) printf '%s\n' 'Usage: scripts/test-verifier.sh [--python-only]' >&2; exit 2 ;;
esac
if [[ $# -ne 0 ]]; then
  printf '%s\n' 'Usage: scripts/test-verifier.sh [--python-only]' >&2
  exit 2
fi

(cd "$ROOT" && python3 -m unittest discover -s verifier/tests -p 'test_*.py')
if "$python_only"; then
  exit 0
fi

COMPARATOR="$ROOT/verifier/.tools/comparator"
if ! command -v lake >/dev/null 2>&1 ||
    [[ ! -f "$COMPARATOR/.lake/build/lib/lean/CertificateCheck.olean" ||
       ! -x "$COMPARATOR/.lake/build/bin/certificate-check" ||
       ! -x "$COMPARATOR/.lake/packages/lean4export/.lake/build/bin/lean4export" ]]; then
  printf '%s\n' 'test-verifier: native Lean tools/checker missing; run verifier/setup_tools.sh first' >&2
  printf '%s\n' 'Use --python-only explicitly to run without native Lean tests.' >&2
  exit 1
fi

(
  cd "$COMPARATOR"
  lake env lean ../../tests/CertificateTests.lean
  # Save an actual accepting report for the small organizer fixture, not sig-golf.
  printf '%s\n' 'Native fixture acceptance report (not full sig-golf verification):'
  .lake/build/bin/certificate-check .lake/certificate-tests/serve-config.json \
    .lake/certificate-tests/serve-trusted.export .lake/certificate-tests/serve-trusted.export \
    .lake/certificate-tests/fixture-report.json
)
printf 'Native fixture report: %s\n' "$COMPARATOR/.lake/certificate-tests/fixture-report.json"
if [[ "$(uname -s)" == Linux ]]; then
  (cd "$ROOT" && SIG_GOLF_NATIVE_TESTS=1 python3 -m unittest discover -s verifier/tests -p test_native_worker.py -v)
fi
