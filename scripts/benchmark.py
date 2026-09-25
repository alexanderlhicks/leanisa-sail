#!/usr/bin/env python3
"""Compare scanning and indexed execution using wall and process CPU clocks."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import statistics

from check import ROOT, command


def host_snapshot():
    return {
        name: path.read_text().strip() if path.exists() else None
        for name, path in (
            ("loadavg", Path("/proc/loadavg")),
            ("cpu_pressure", Path("/proc/pressure/cpu")),
        )
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sail-root", type=Path, default=ROOT.parent / "sail")
    parser.add_argument("--samples", type=int, default=5)
    args = parser.parse_args()
    if args.samples < 1:
        parser.error("--samples must be positive")
    sail_root = args.sail_root.resolve()
    build = ROOT / "build/benchmark"
    build.mkdir(parents=True, exist_ok=True)
    report_path = build / "results.json"
    report_path.unlink(missing_ok=True)
    env = dict(os.environ)
    env["PATH"] = str(sail_root / "_deps/z3/bin") + os.pathsep + env["PATH"]
    files = [ROOT / "spec" / f for f in ("field.sail", "blake2s.sail", "machine.sail", "encoding.sail")]
    files += [ROOT / "tests/addressing.sail", ROOT / "tests/benchmark.sail"]
    measured_sources = files + [ROOT / "tests/benchmark-clock.c", ROOT / "tests/benchmark-clock.h", Path(__file__).resolve()]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in measured_sources}
    binary = build / "benchmark"
    command([
        sail_root / "sail", "--memo-z3-path", build / "smt-cache", "-c", "-O",
        "--c-include", ROOT / "tests/benchmark-clock.h", *files, "-o", binary,
    ], env=env)
    runtime = sail_root / "lib"
    command([
        "cc", "-O2", "-I", runtime, binary.with_suffix(".c"), ROOT / "tests/benchmark-clock.c",
        *[runtime / f for f in ("sail.c", "rts.c", "elf.c", "sail_failure.c")], "-lgmp", "-o", binary,
    ], env=env)
    before = host_snapshot()
    runs = []
    for trial in range(args.samples + 1):
        result = command([binary], env=env, capture=True, timeout=120)
        samples = [json.loads(line) for line in result.stdout.splitlines()]
        runs.append({"warmup": trial == 0, "samples": samples})
        print(f"{'Warmup' if trial == 0 else f'Sample {trial}'} complete", flush=True)
    after = host_snapshot()
    summary = {}
    for sample in runs[0]["samples"]:
        case = sample["case"]
        summary[case] = {}
        for clock in ("wall_ns", "cpu_ns"):
            values = [s[clock] / 1e6 for r in runs[1:] for s in r["samples"] if s["case"] == case]
            summary[case][clock.replace("_ns", "_ms")] = {
                "median": statistics.median(values), "min": min(values), "max": max(values),
            }
    for relative, digest in hashes.items():
        if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != digest:
            raise RuntimeError(f"{relative} changed during benchmarking; rerun against stable sources")
    report = {
        "completed_utc": datetime.now(timezone.utc).isoformat(),
        "method": "One warmup, then repeated runs; 64 reads per lookup case. Run cases include index construction. "
                  "Both paths use identical Sail -O and cc -O2 settings, without coverage instrumentation. "
                  "Process CPU time excludes descheduling but still reflects shared-resource and frequency effects.",
        "sail": command([sail_root / "sail", "--version"], env=env, capture=True).stdout.strip(),
        "cc": command(["cc", "--version"], capture=True).stdout.splitlines()[0],
        "source_sha256": hashes, "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "host_before": before, "host_after": after, "runs": runs, "summary": summary,
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    for case, timing in summary.items():
        print(f"{case:24s} wall {timing['wall_ms']['median']:10.3f} ms   CPU {timing['cpu_ms']['median']:10.3f} ms")
    print(f"Results: {report_path}")


if __name__ == "__main__":
    main()
