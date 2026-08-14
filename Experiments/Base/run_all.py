"""Run the isolated experiment suite and the standalone Lean check."""

from __future__ import annotations

import importlib
import json
import subprocess
import sys
from pathlib import Path


EXPERIMENT_MODULES = [
    "jointly_controlled_group_lottery",
    "inhomogeneous_hazard_scheduler",
    "path_complete_livsic",
    "atlas_progress_analyzer",
    "arc_orientation_scan",
    "owner_monodromy",
    "kelly_debt_boundary",
    "causal_state_minimizer",
    "small_game_census",
    "continuous_time_resolvent",
    "collateral_account",
    "predictive_compression",
    "sigma_delta_lottery",
    "abel_turnpike_retargeting",
    "multiscale_filter_bank",
    "transition_algebra",
    "player_representation",
    "cyclic_fourier_abel_cesaro",
    "markov_hodge_currents",
    "adiabatic_markov_tracking",
    "metastable_schur_confluence",
    "thermal_equilibrium_selection",
    "entropy_current_debt",
    "common_reversible_dirichlet",
    "finite_controller_cycle_verifier",
    "exact_rate_memory_blowup",
    "contextual_cycle_sat",
    "commit_reveal_coin",
    "threshold_secret_sharing",
    "live_entropy_budget",
]

LEAN_EXPERIMENTS = [
    ("E09", "SignedTargetTransport.lean", "Standalone Lean signed-target transport compiled."),
    ("E13", "LedgeredDissipativity.lean", "Standalone Lean ledgered dissipativity theorem compiled."),
    ("E21", "EquivariantAveraging.lean", "Standalone Lean Reynolds averaging theorems compiled."),
]


def main() -> None:
    directory = Path(__file__).resolve().parent
    repo = directory.parent.parent
    sys.path.insert(0, str(directory))

    results = []
    for module_name in EXPERIMENT_MODULES:
        module = importlib.import_module(module_name)
        if module_name == "atlas_progress_analyzer":
            result = module.analyze(repo)
        else:
            result = module.run()
        assert result["status"] == "passed"
        results.append(
            {
                "experiment": result["experiment"],
                "status": result["status"],
                "conclusion": result["conclusion"],
            }
        )

    for experiment, filename, conclusion in LEAN_EXPERIMENTS:
        lean_file = directory / filename
        lean = subprocess.run(
            ["lake", "env", "lean", str(lean_file)],
            cwd=repo,
            capture_output=True,
            text=True,
            check=False,
        )
        if lean.returncode != 0:
            raise RuntimeError(lean.stdout + lean.stderr)
        results.append(
            {
                "experiment": experiment,
                "status": "passed",
                "conclusion": conclusion,
            }
        )

    results.sort(key=lambda result: int(result["experiment"][1:]))
    print(
        json.dumps(
            {
                "status": "passed",
                "experiment_count": len(results),
                "results": results,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
