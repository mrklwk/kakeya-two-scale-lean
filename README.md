# Two-scale Kakeya upper Minkowski lower bound

We prove that every bounded Kakeya set in $\mathbb R^n$, $n\ge4$, has upper Minkowski dimension at least $0.597n$. Here a Kakeya set contains a unit line segment in every direction. This improves the asymptotic coefficient $c_{\mathrm{KT}}=1/\alpha=0.596968283237\ldots$ in the Katz--Tao bound $1+c_{\mathrm{KT}}(n-1)$, where $\alpha$ is the unique root of $\alpha^3-4\alpha+2=0$ in $(1,2)$. The proof combines arithmetic estimates for line segments with geometric estimates for tubes at two different widths.

Project author and sole human responsible maintainer: Mark Lewko. Codex assisted with Lean formalization, proof-closure inspection and documentation. No human peer review is claimed. Upstream attribution is retained.

For the finite-dimensional comparison, 0.597n exceeds the full Katz–Tao bound
1 + c_KT(n − 1) exactly for integer n ≥ 12708. For 4 ≤ n ≤ 12707, the Katz–Tao
bound is larger. COMPARISON.json records the exact rational checks. No claim of
superiority to all later results is made. The exported endpoint remains 597n/1000.

The selected theorem is `PalomarKakeya.upperMinkowski_lower` in `Solution.lean`.
It applies to bounded subsets of real Euclidean n-space, n ≥ 4, containing a
translated closed unit segment in every direction. The translation may depend
on the direction. The conclusion uses least finite covers by open Euclidean
balls and the limsup through all positive radii tending to zero. No extra
analytic, measurability, closedness, or compactness hypothesis is assumed.
No Hausdorff or lower Minkowski conclusion is claimed.

`Challenge.lean` states the theorem independently and contains one intentional
statement hole. `Solution.lean` supplies the closed proof. The proof sources have
no holes and use only propext, Classical.choice, and Quot.sound.

The pinned pair is Lean 4.35.0-rc2 and mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55. All nine Lake dependencies have immutable
revision pins. With the pinned toolchain on PATH, build with:

```sh
lake build Challenge Solution
```

On Linux with bubblewrap and the toolchain's bundled verifiers on PATH, run:

```sh
lake comparator
```

The submitted comparator.json enables NanoDa. The recorded protected verification
also registered bundled con-ron in verified mode through a separate verifier-owned
configuration. To repeat that checker set, copy comparator.json, remove
enable_nanoda, and set external_kernels to the commands in PUBLIC_VERIFICATION.json;
then run `lake comparator --config <configuration>`. Keep the stock sandbox enabled.

PUBLIC_VERIFICATION.json records the completed checker scope. The selected build
has 1,049 project dependency modules plus Challenge and Solution. Six additional
checkpoint or auxiliary files are included outside that import graph. All 1,057
Lean files match the checked source snapshot. The theorem-level verification does
not claim to export every auxiliary declaration.

Mark Lewko's original project material is licensed AGPL-3.0-only. Upstream
material retains its original notices and terms. LICENSE, NOTICE, and
THIRD_PARTY_NOTICES.md describe the scope. Vendored source-lock files describe
the pre-module-system sources; MIGRATION_SOURCE_MAP.json records the subsequent
module conversion and compatibility repairs. verification/PROOF_SOURCE_SHA256.json
binds the current 1,057 Lean files, and RELEASE_SHA256.json lists all release files
except that manifest itself.
