# HamSandwich dependency

Upstream: https://github.com/akopjan/HamSandwich
Pinned revision: 76202dbbb6610ffcebbccfbf7a56f833a4c2a376.
The upstream Apache-2.0 LICENSE is preserved byte for byte. No upstream NOTICE
file was present. Existing copyright, author and license notices are retained.

This directory contains the 170-module Borsuk–Ulam dependency cone. The local
compatibility port began with upstream Lean 4.28.0 and was subsequently migrated
to the root project's pinned Lean 4.35.0-rc2/mathlib pair. Modified files retain
their modification notices. Five obsolete prism-backport modules were replaced
by existing mathlib APIs.

source-lock.json records upstream, reviewed-port, and pre-module-system vendored
hashes. MIGRATION_SOURCE_MAP.json records subsequent module conversion and
compatibility repairs. Current file hashes are listed in
verification/PROOF_SOURCE_SHA256.json. The root Lakefile preserves this library's
compiler options. No upstream build hook is executed.
