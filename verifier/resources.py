"""Validated organizer-only resource settings; never read candidate configuration."""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import os
from pathlib import Path
from typing import Mapping

GIB = 1024**3
PROFILES = {"conservative": (2, 24), "balanced": (4, 40), "large": (8, 80)}


@dataclass(frozen=True)
class ResourceProfile:
    name: str
    cpus: int
    memory_bytes: int
    build_jobs: int
    lean_threads: int
    cpu_affinity: tuple[int, ...]


def available_memory_bytes() -> int:
    """Physical RAM, further restricted by any visible cgroup memory limit."""
    lines = Path("/proc/meminfo").read_text().splitlines()
    memory = next(int(line.split()[1]) * 1024 for line in lines if line.startswith("MemTotal:"))
    limits = [Path("/sys/fs/cgroup/memory.max")]
    for line in Path("/proc/self/cgroup").read_text().splitlines():
        if line.startswith("0::"):
            root = Path("/sys/fs/cgroup")
            path = root / line[3:].lstrip("/")
            if ".." not in path.parts:
                limits.extend(parent / "memory.max" for parent in (path, *path.parents) if parent == root or root in parent.parents)
    for path in limits:
        if path.is_file():
            value = path.read_text().strip()
            if value != "max":
                memory = min(memory, int(value))
    return memory


def _integer(env: Mapping[str, str], name: str, default: int, minimum: int, maximum: int) -> int:
    value = env.get(name, str(default))
    if not value or not value.isascii() or not value.isdecimal() or len(value) > 10:
        raise ValueError(f"{name} must be an unsigned decimal integer")
    number = int(value)
    if not minimum <= number <= maximum:
        raise ValueError(f"{name} must be between {minimum} and {maximum}")
    return number


def resource_profile(environ: Mapping[str, str] | None = None, *,
                     available_cpus: tuple[int, ...] | None = None,
                     memory_limit_bytes: int | None = None) -> ResourceProfile:
    """Resolve trusted environment fields, retaining the historical 2 CPU/24 GiB default.

    Reserve at least 4 GiB for the guest OS and verifier outside the candidate cgroup.
    Explicit capacity arguments support callers validating a planned VM and unit tests.
    """
    env = os.environ if environ is None else environ
    name = env.get("SIG_VERIFY_PROFILE", "conservative")
    if name not in PROFILES:
        raise ValueError("SIG_VERIFY_PROFILE must be conservative, balanced, or large")
    affinity = tuple(sorted(os.sched_getaffinity(0))) if available_cpus is None else tuple(sorted(set(available_cpus)))
    if not affinity:
        raise ValueError("no CPUs are available for verification")
    memory = available_memory_bytes() if memory_limit_bytes is None else memory_limit_bytes
    default_cpus, default_memory = PROFILES[name]
    cpus = _integer(env, "SIG_VERIFY_CPUS", default_cpus, 1, len(affinity))
    memory_gib = _integer(env, "SIG_VERIFY_MEMORY_GIB", default_memory, 4, (memory - 4 * GIB) // GIB)
    jobs = _integer(env, "SIG_VERIFY_BUILD_JOBS", min(4, len(affinity)), 1, len(affinity))
    threads = _integer(env, "SIG_VERIFY_LEAN_THREADS", 1, 1, min(2, len(affinity)))
    return ResourceProfile(name, cpus, memory_gib * GIB, jobs, threads, affinity[:cpus])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vm", action="store_true", help="validate planned VM and reserve 8 GiB on the host")
    args = parser.parse_args()
    try:
        vm_cpus = vm_memory = None
        if args.vm:
            vm_cpus = _integer(os.environ, "SIG_VERIFY_VM_CPUS", 12, 1, len(os.sched_getaffinity(0)))
            vm_memory = _integer(os.environ, "SIG_VERIFY_VM_MEMORY_GIB", 48, 8, (available_memory_bytes() - 8 * GIB) // GIB)
        profile = resource_profile(available_cpus=tuple(range(vm_cpus)) if vm_cpus is not None else None,
                                   memory_limit_bytes=vm_memory * GIB if vm_memory is not None else None)
    except (ValueError, OSError, StopIteration) as error:
        parser.exit(2, f"invalid verifier resources: {error}\n")
    # These allowlisted enum/numeric assignments are safe to pass through SSH's shell.
    print(f"SIG_VERIFY_PROFILE={profile.name}")
    print(f"SIG_VERIFY_CPUS={profile.cpus}")
    print(f"SIG_VERIFY_MEMORY_GIB={profile.memory_bytes // GIB}")
    print(f"SIG_VERIFY_BUILD_JOBS={profile.build_jobs}")
    print(f"SIG_VERIFY_LEAN_THREADS={profile.lean_threads}")
    if args.vm:
        print(f"SIG_VERIFY_VM_CPUS={vm_cpus}")
        print(f"SIG_VERIFY_VM_MEMORY_GIB={vm_memory}")


if __name__ == "__main__":
    main()
