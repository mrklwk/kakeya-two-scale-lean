# Szemerédi source dependency

Upstream: https://github.com/gdahia/DensityHalesJewett
Pinned commit: 1c2f5aa1b99caa8e2a87beacf80f07f066c309d3.
Author: Gabriel Dahia. Apache-2.0; see LICENSE and per-file notices.

The 13-module import closure of DensityHalesJewett.Szemeredi is vendored.
source-lock.json records the upstream and pre-module-system source hashes.
The upstream selects Lean 4.34.0 and mathlib
56a9a88447f391672d7aeea117da03b6f7016b0d; upstream-lake-manifest.json and
upstream-lean-toolchain retain those original pins.

The current project uses Lean 4.35.0-rc2 and the matching mathlib revision in
the root lake-manifest.json. MIGRATION_SOURCE_MAP.json records the intervening
module conversion and compatibility changes. The root Lakefile preserves the
library-specific compiler options. Current file hashes are listed in
verification/PROOF_SOURCE_SHA256.json.
