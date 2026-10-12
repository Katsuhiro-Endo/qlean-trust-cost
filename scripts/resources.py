#!/usr/bin/env python3
"""Evaluate the published input without expanding the full QSP gate list."""
from pathlib import Path
import os
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
subprocess.run(["lake", "build", "paperResources"], cwd=root, check=True)
binary = root / ".lake/build/bin" / ("paperResources.exe" if os.name == "nt" else "paperResources")
result = subprocess.run([str(binary)], cwd=root, text=True,
    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(result.stdout, end="")
(root / "build").mkdir(exist_ok=True)
(root / "build/resource-counts.txt").write_text(result.stdout, encoding="utf-8")
if result.returncode:
    raise SystemExit(result.returncode)
expected = {
    "cp01_qubits": "124", "cp01_gates": "16041",
    "cp02_qubits": "275", "cp02_gates": "40197",
    "cp03_cp04_qubits": "3342", "cp03_cp04_gates": "417312971982202",
    "qsp_degree": "3125001", "qsp_phase_count": "3125002",
    "signalCost": "696587", "phaseCost": "32688427",
}
observed = dict(line.split("=", 1) for line in result.stdout.splitlines() if "=" in line)
differences = {key: (value, observed.get(key)) for key, value in expected.items()
               if observed.get(key) != value}
if differences:
    raise SystemExit(f"Resource counts differ from the paper instance (expected, observed): {differences}")
print("All resource counts match the paper instance.")
