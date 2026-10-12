#!/usr/bin/env python3
"""Compile separated source layers without requiring the opposite layer.

External dependencies are managed by Lake. Project modules are compiled into
one namespace-compatible output tree for each selected target.
"""
from pathlib import Path
import argparse
import concurrent.futures
import graphlib
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
LAYERS = ["common-mathematics", "mathematical-specifications", "circuits", "correspondence"]
ALLOWED = {
    "common-mathematics": {"common-mathematics"},
    "mathematical-specifications": {"common-mathematics", "mathematical-specifications"},
    "circuits": {"common-mathematics", "circuits"},
    "correspondence": set(LAYERS),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", choices=["math", "circuits", "all"])
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    selected = {"math": {"common-mathematics", "mathematical-specifications"},
                "circuits": {"common-mathematics", "circuits"},
                "all": set(LAYERS)}[args.target]
    modules = {}
    for layer in LAYERS:
        for path in (ROOT / layer / "src").rglob("*.lean"):
            name = ".".join(path.relative_to(ROOT / layer / "src").with_suffix("").parts)
            if name in modules:
                raise RuntimeError(f"Duplicate module: {name}")
            modules[name] = (layer, path)
    chosen = {m: data for m, data in modules.items() if data[0] in selected}
    if not chosen:
        raise RuntimeError("No Lean sources found; this is not a completed source distribution.")
    dependencies = {}
    for name, (layer, path) in chosen.items():
        imports = re.findall(r"^import\s+(\S+)", path.read_text(encoding="utf-8"), re.M)
        for imp in imports:
            if imp in modules and modules[imp][0] not in ALLOWED[layer]:
                raise RuntimeError(f"Forbidden cross-layer import: {name} -> {imp}")
            if imp.startswith(("QLean.", "VerifiedMath.")) and imp not in modules:
                raise RuntimeError(f"Missing project module: {name} -> {imp}")
        dependencies[name] = set(imports) & chosen.keys()
    build = ROOT / "build" / args.target
    lib = build / "lib"
    logs = build / "logs"
    lib.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    lake_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
    external = [p for p in lake_path.split(os.pathsep) if ".lake/packages/" in p.replace("\\", "/")]
    if not external:
        raise RuntimeError("External dependency paths missing. Run lake update and lake exe cache get.")
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([str(lib)] + external)
    env["LEAN_NUM_THREADS"] = "1"
    statefile = build / "verified.json"
    state = json.loads(statefile.read_text()) if statefile.exists() else {}
    signatures = {}
    for name in graphlib.TopologicalSorter(dependencies).static_order():
        signatures[name] = hashlib.sha256(chosen[name][1].read_bytes() +
            "".join(signatures[d] for d in sorted(dependencies[name])).encode()).hexdigest()

    def compile_one(name):
        layer, path = chosen[name]
        output = lib.joinpath(*name.split(".")).with_suffix(".olean")
        if state.get(name) == signatures[name] and output.exists():
            return True
        print(f"Checking {name}", flush=True)
        output.parent.mkdir(parents=True, exist_ok=True)
        logfile = logs / (name + ".log")
        with logfile.open("w", encoding="utf-8") as log:
            result = subprocess.run(["lean", "--root=" + str(ROOT / layer / "src"),
                "-o", str(output), str(path)], cwd=ROOT, env=env,
                stdout=log, stderr=subprocess.STDOUT)
        if result.returncode:
            print(logfile.read_text(encoding="utf-8", errors="replace"), file=sys.stderr)
            return False
        return True

    sorter = graphlib.TopologicalSorter(dependencies)
    sorter.prepare()
    running, ready, failed = {}, [], []
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        while sorter.is_active() or running:
            ready.extend(sorter.get_ready())
            while ready and len(running) < max(1, args.jobs) and not failed:
                name = ready.pop(0)
                running[pool.submit(compile_one, name)] = name
            if not running:
                break
            finished, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                name = running.pop(future)
                if future.result():
                    state[name] = signatures[name]
                    sorter.done(name)
                    statefile.write_text(json.dumps(state, indent=2))
                else:
                    failed.append(name)
            if failed and not running:
                break
    if failed:
        raise SystemExit("FAILED: " + ", ".join(failed))
    print(f"Verified {len(chosen)} modules for {args.target}.")


if __name__ == "__main__":
    main()
