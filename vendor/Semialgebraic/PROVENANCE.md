# Pinned semialgebraic dependency

Source: openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
lean/OAI/Analysis/SymmetricDomains. The Apache-2.0 license is retained in LICENSE.
The upstream lean-toolchain was leanprover/lean4:v4.34.1. The current project uses
the Lean 4.35.0-rc2/mathlib pair pinned at the root.

The 25-file closure covers real polynomial-sign projection via Hermite signature,
Tarski queries and chamber sampling, finite-dimensional definable choice, and
scalar analyticity outside a nonzero polynomial zero locus. order.json records
the dependency order. source-lock.json records upstream and pre-module-system
admitted source hashes and modification flags.

The local adaptation removed unused complex-analytic imports from nine files.
GenericAlgebraicRamificationUniform retains semialgebraic_function_analytic_off_polynomial
with its two resultant helper proofs from IntegralPrimitive and
GenericFinParameterPolynomial. Existing per-file modification notices are retained.

MIGRATION_SOURCE_MAP.json records the subsequent module conversion and
compatibility repairs. Current file hashes are listed in
verification/PROOF_SOURCE_SHA256.json. Only the admitted 25-file closure is a
source root in this project.
