#!/usr/bin/env bash
# The Blacksmith host lacks Landlock. Boot the verifier's supported OS with KVM.
set -euo pipefail
cd "$(dirname "$0")/.."
vm="${RUNNER_TEMP:?This entry point runs in GitHub Actions}/sig-verifier-vm"
ssh_args=(-i "${vm}/key" -p 2222 -o BatchMode=yes -o ConnectTimeout=5
  -o ServerAliveInterval=15 -o ServerAliveCountMax=4
  -o StrictHostKeyChecking=accept-new -o UserKnownHostsFile="${vm}/known_hosts")
# Callers supply only fixed commands.
# shellcheck disable=SC2029
guest() { ssh "${ssh_args[@]}" ubuntu@127.0.0.1 "$@"; }

case "${1:-}" in
  start)
    test -c /dev/kvm || { echo 'Blacksmith x64 nested KVM is required' >&2; exit 1; }
    sudo apt-get update -qq
    sudo apt-get install -y --no-install-recommends qemu-system-x86 qemu-utils cloud-image-utils
    mkdir -m 700 "${vm}"
    curl --fail --location --retry 3 \
      https://cloud-images.ubuntu.com/releases/resolute/release-20260918/ubuntu-26.04-server-cloudimg-amd64.img \
      -o "${vm}/ubuntu.img"
    echo "4908fb59ccd4e87ae4e8e973b7ef56f535448eacb24a87fd787270c0048987bc  ${vm}/ubuntu.img" | sha256sum --check
    qemu-img create -f qcow2 -F qcow2 -b "${vm}/ubuntu.img" "${vm}/root.qcow2" 100G
    ssh-keygen -q -t ed25519 -N '' -f "${vm}/key"
    cat > "${vm}/user-data" <<CLOUD
#cloud-config
ssh_authorized_keys:
  - $(cat "${vm}/key.pub")
package_update: true
packages:
  - git
  - curl
  - build-essential
  - python3
  - golang-go
  - dbus-user-session
  - apparmor
  - zstd
CLOUD
    printf 'instance-id: sig-verifier\nlocal-hostname: sig-verifier\n' > "${vm}/meta-data"
    cloud-localds "${vm}/seed.img" "${vm}/user-data" "${vm}/meta-data"
    sudo qemu-system-x86_64 -accel kvm -cpu host -smp 12 -m 32G \
      -drive "file=${vm}/root.qcow2,if=virtio,format=qcow2" \
      -drive "file=${vm}/seed.img,if=virtio,format=raw,readonly=on" \
      -netdev user,id=net0,hostfwd=tcp:127.0.0.1:2222-:22 -device virtio-net-pci,netdev=net0 \
      -display none -serial "file:${vm}/console.log" -monitor none \
      -daemonize -pidfile "${vm}/qemu.pid"
    ready=0
    for ((attempt=0; attempt<120; attempt++)); do
      if guest true 2>/dev/null; then ready=1; break; fi
      sleep 2
    done
    if [[ "${ready}" != 1 ]]; then sudo cat "${vm}/console.log"; exit 1; fi
    guest 'sudo cloud-init status --wait'
    # Credentials were removed by checkout; only the checkout enters the VM.
    tar --exclude='./.work' --exclude='./.cache' -cf - . | \
      guest 'sudo mkdir -p /srv/sig-benchmark && sudo tar -xf - -C /srv/sig-benchmark'
    ;;
  setup)
    guest 'sudo bash /srv/sig-benchmark/scripts/vm-setup.sh'
    if [[ -f .cache/trusted.tar.zst ]]; then
      guest 'sudo tar --zstd -xf - -C /srv' < .cache/trusted.tar.zst
      guest 'sudo chown -R sig:sig /srv/sig /srv/sig-benchmark'
    fi
    # shellcheck disable=SC2016 # Resolve the judge UID inside the guest.
    guest 'cd /srv/sig-benchmark && sudo -u sig -H env XDG_RUNTIME_DIR=/run/user/$(id -u sig) bash scripts/setup.sh'
    ;;
  cache)
    mkdir -p .cache
    # Export before any candidate code runs; only trusted dependency/build trees.
    guest 'sudo tar --zstd -C /srv -cf - sig/.elan sig-benchmark/.lake sig-benchmark/verifier/.tools' > .cache/trusted.tar.zst
    ;;
  run)
    # shellcheck disable=SC2016 # Resolve the judge UID inside the guest.
    guest 'cd /srv/sig-benchmark && sudo -u sig -H env PATH=/srv/sig/.elan/bin:/usr/local/bin:/usr/bin:/bin XDG_RUNTIME_DIR=/run/user/$(id -u sig) python3 scripts/run.py'
    ;;
  collect)
    if [[ -f "${vm}/qemu.pid" ]]; then
      sudo cat "${vm}/console.log" | tee .work-vm-console.log >/dev/null
      guest 'cd /srv/sig-benchmark && sudo mkdir -p .work && sudo find scripts .work -type f \( -name score.json -o -name verify.log \) -print0 | sudo tar --null -T - -cf -' | tar -xf -
    fi
    ;;
  stop)
    if [[ -f "${vm}/qemu.pid" ]]; then sudo kill "$(sudo cat "${vm}/qemu.pid")"; fi
    ;;
  *) echo 'Usage: blacksmith.sh start | setup | cache | run | collect | stop' >&2; exit 2 ;;
esac
