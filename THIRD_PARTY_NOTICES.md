# Upstream notices

The root AGPL-3.0-only choice applies to Mark Lewko's original project material.
Upstream material retains its original notices and terms. Local migration and
compatibility changes are recorded in MIGRATION_SOURCE_MAP.json; upstream
source locks describe the pre-module-system versions. Current Lean file hashes
are listed in verification/PROOF_SOURCE_SHA256.json.

| Material | Pinned upstream | License retained |
| --- | --- | --- |
| DensityHalesJewett | gdahia/DensityHalesJewett, 1c2f5aa1b99caa8e2a87beacf80f07f066c309d3 | vendor/DensityHalesJewett/LICENSE, Apache-2.0 |
| HamSandwich | akopjan/HamSandwich, 76202dbbb6610ffcebbccfbf7a56f833a4c2a376 | vendor/HamSandwich/LICENSE, Apache-2.0 |
| Semialgebraic subset | openai/math, fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb | vendor/Semialgebraic/LICENSE, Apache-2.0 |

Lean, mathlib, and their Lake dependencies are pinned in lean-toolchain and
lake-manifest.json. They are fetched separately and keep their own upstream
license files. No dependency binaries or installed toolchains form part of this
source release. No upstream author endorsement is claimed.
