module
public import KakeyaTwoScale.LocalizedAxisTruncation
public import KakeyaTwoScale.ActualArchiveLocalization

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState
variable {n k : ℕ} {T C O : Type}

/-- An actual descendant selects a long ancestor-axis witness near the
concentric truncated zero set. All length comparisons and the common-ball
witness are proved from physical containment and state localization. -/
theorem localized_ancestor_axis (S U : FrozenGeometryState n k T C O)
    (cube : T→C) (tube : T→Fin k→O) (δ rho C0 : ℝ) (hδ : 0<δ) (hC : 0≤C0)
    (hS : BufferedArchiveSnapshot.Certified δ tube (BufferedArchiveSnapshot.ofState S))
    (hU : BufferedArchiveSnapshot.Certified δ tube (BufferedArchiveSnapshot.ofState U))
    (hsub : U.tuples⊆S.tuples)
    (hcontain : ∀ y∈U.tuples, ∀ j, U.geometry δ j (U.parent y j) ⊆ S.geometry δ j (S.parent y j))
    (haxis : ∀ y∈U.tuples, ∀ j, U.axis j (U.parent y j)=S.axis j (S.parent y j))
    (hlocal : BufferedArchiveSnapshot.Localized δ cube (BufferedArchiveSnapshot.ofState U))
    (V : S.Grain→Set (EuclideanSpace ℝ (Fin n)))
    (hcapture : ∀ y∈S.tuples, ∀ j, S.geometry δ j (S.parent y j) ⊆ thickening rho (V (S.grain (cube y))))
    (j : Fin k) (hradius : U.ballRadius≤C0*U.length δ j) (hlong : 8*rho≤U.length δ j) :
    ∀ y∈U.tuples,
      let center := U.ballCenter (U.grain (cube y))
      let L := S.length δ j
      let Z := V (S.grain (cube y)) ∩ closedBall center ((C0+4)*L)
      (∀ t∈Icc (L/4) (3*L/4),
        S.base j (S.parent y j)+t • S.axis j (S.parent y j)∈thickening rho Z) ∧
      L/4≤diam Z ∧ diam Z≤2*(C0+4)*L := by
  classical
  intro y hy
  have hell : 0<U.length δ j := by unfold length; positivity
  have hL : 0<S.length δ j := by unfold length; positivity
  have hc := hcontain y hy j
  unfold geometry at hc
  rw [haxis y hy j] at hc
  have hl := disjoint_contained_cylinders_length_sum ({0}:Finset ℕ)
    (S.base j (S.parent y j)) (S.axis j (S.parent y j))
    (fun _=>U.base j (U.parent y j)) (fun _=>U.length δ j)
    (S.length δ j) δ (hS.2.1 j _) hL hδ (fun _ _=>hell) (fun _ _=>hc) (by simp)
  simp only [Finset.sum_singleton] at hl
  have hδL : δ≤S.length δ j := by
    have hh := one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=S.height j)
    exact (by simpa only [mul_one,length] using mul_le_mul_of_nonneg_left hh hδ.le)
  obtain ⟨w,hw⟩ := hU.2.2.2.1 y hy j
  have hwball := hlocal y hy j hw
  change dist w (U.ballCenter (U.grain (cube y))) < U.ballRadius at hwball
  exact localized_axis_truncation (S.base j (S.parent y j)) (S.axis j (S.parent y j))
    (U.ballCenter (U.grain (cube y))) w (V (S.grain (cube y)))
    (S.length δ j) (U.length δ j) δ rho C0 (hS.2.1 j _) hL hδ hδL hl hC
    (hlong.trans hl) (hcontain y hy j hw) (hwball.trans_le hradius) (hcapture y (hsub hy) j)

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.localized_ancestor_axis
