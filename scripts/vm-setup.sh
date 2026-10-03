#!/usr/bin/env bash
# Trusted bootstrap in the fresh Ubuntu 26.04 guest, before any proof is compiled.
set -euo pipefail
cd /srv/sig-benchmark
SECONDS=0
trap 'status=$?; printf "VM bootstrap: elapsed_seconds=%s exit_code=%s\n" "${SECONDS}" "${status}"' EXIT
# Validate against actual guest affinity/RAM, not just the planned host allocation.
python3 verifier/resources.py
systemctl --version
cat /sys/kernel/security/lsm
test "$(systemctl --version | head -1 | awk '{print $2}')" -ge 257
grep -qw landlock /sys/kernel/security/lsm
# ProtectSystem=strict excludes /home; keep the judge home under /srv, as upstream does.
useradd --create-home --home-dir /srv/sig --shell /bin/bash sig
chown -R sig:sig /srv/sig-benchmark
loginctl enable-linger sig
systemctl start "user@$(id -u sig).service"
cat > /etc/apparmor.d/sig-systemd-executor <<'APPARMOR'
abi <abi/4.0>,
include <tunables/global>
profile sig-systemd-executor /usr/lib/systemd/systemd-executor flags=(unconfined) {
  userns,
  include if exists <local/sig-systemd-executor>
}
APPARMOR
apparmor_parser -r /etc/apparmor.d/sig-systemd-executor
