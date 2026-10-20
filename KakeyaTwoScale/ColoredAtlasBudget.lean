module
public import KakeyaTwoScale.TranslatedDirectionalArea

@[expose] public section

open Set MeasureTheory
open scoped ENNReal Function
noncomputable section
namespace KakeyaTwoScale

/-- Empty localization has zero actual area, without a finiteness assumption. -/
theorem DisjointChartAtlas.restrict_empty_area {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) (v : Fin (n+1) → ℝ) :
    (A.restrict ∅ MeasurableSet.empty).directionalArea v=0 := by
  change (∑' k, ∫⁻ x in A.piece k ∩ (A.chart k).map ⁻¹' ∅,
    ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart k).map x) v|)=0
  simp

/-- A finite disjointness coloring pays its actual number of colors. It does
not discard hypersurface mass on shared cube boundaries. -/
theorem DisjointChartAtlas.colored_restrict_area_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} {Z : Set (Fin (n+1) → ℝ)} (A : DisjointChartAtlas n Z)
    (E : ι → Set (Fin (n+1) → ℝ)) (hE : ∀i, MeasurableSet (E i))
    (color : ι → κ)
    (hd : ∀i j, i≠j → color i=color j → Disjoint (E i) (E j))
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (hEU : ∀i, E i⊆U)
    (v : Fin (n+1) → ℝ) :
    (∑i, (A.restrict (E i) (hE i)).directionalArea v) ≤
      (Fintype.card κ : ℝ≥0∞)*(A.restrict U hU).directionalArea v := by
  classical
  let F (c : κ) (i : ι) := if color i=c then E i else ∅
  have hF (c i) : MeasurableSet (F c i) := by
    dsimp [F]; split_ifs <;> simp [hE]
  have he (c i) : (A.restrict (F c i) (hF c i)).directionalArea v =
      if color i=c then (A.restrict (E i) (hE i)).directionalArea v else 0 := by
    by_cases hc : color i=c
    · simp [F,hc,DisjointChartAtlas.directionalArea,DisjointChartAtlas.restrict]
    · simp [F,hc,DisjointChartAtlas.directionalArea,DisjointChartAtlas.restrict]
  have hb (c) : (∑i, (A.restrict (F c i) (hF c i)).directionalArea v) ≤
      (A.restrict U hU).directionalArea v := by
    apply A.sum_restrict_area_le _ (hF c)
    · intro i j hij
      dsimp [Function.onFun,F]
      split_ifs with hi hj
      · exact hd i j hij (hi.trans hj.symm)
      all_goals simp
    · intro i
      dsimp [F]
      split_ifs
      · exact hEU i
      · exact empty_subset _
  calc
    _ = ∑c, ∑i, (A.restrict (F c i) (hF c i)).directionalArea v := by
      simp_rw [he]
      rw [Finset.sum_comm]
      simp
    _ ≤ ∑_c : κ, (A.restrict U hU).directionalArea v := Finset.sum_le_sum (fun c _ => hb c)
    _ = _ := by simp [nsmul_eq_mul]

def latticeCubeColor {N : ℕ} (z : Fin N → ℤ) : Fin N → Fin 2 :=
  fun i => ⟨(z i%2).toNat, by omega⟩

/-- Same-parity distinct integer cubes are disjoint even as closed sets. -/
theorem latticeCube_same_color_disjoint {N : ℕ} (z w : Fin N → ℤ)
    (hne : z≠w) (hc : latticeCubeColor z=latticeCubeColor w) :
    Disjoint (visibilityCube (fun i => (z i:ℝ))) (visibilityCube (fun i => (w i:ℝ))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hne
  funext i
  have hx' := (dist_pi_le_iff (by norm_num : (0:ℝ)≤1/2)).mp hx i
  have hy' := (dist_pi_le_iff (by norm_num : (0:ℝ)≤1/2)).mp hy i
  rw [Real.dist_eq,abs_le] at hx' hy'
  have hlow : (w i:ℝ)-1≤(z i:ℝ) := by linarith
  have hhigh : (z i:ℝ)≤(w i:ℝ)+1 := by linarith
  have hl : w i-1≤z i := by exact_mod_cast hlow
  have hh : z i≤w i+1 := by exact_mod_cast hhigh
  have hm := congrArg (fun c => (c i).val) hc
  change (z i%2).toNat=(w i%2).toNat at hm
  omega

/-- The closed lattice boundary payment is exactly 2^(n+1), independently
of the number of cubes. The projection region can be anywhere in space. -/
theorem polynomial_lattice_projection_budget {ι : Type*} [Fintype ι] {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P≠0)
    (A : DisjointChartAtlas n {x | MvPolynomial.eval x P=0})
    (z : ι → Fin (n+1) → ℤ) (hz : Function.Injective z)
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (D : Set (Fin n → ℝ)) (hD : MeasurableSet D)
    (hproj : ∀i x, x∈visibilityCube (fun j => (z i j:ℝ)) →
      transverseProjection n ((orthogonalCoordinates R).symm x)∈D) :
    (∑i, (A.restrict (visibilityCube (fun j => (z i j:ℝ))) measurableSet_closedBall).directionalArea
      (orthogonalCoordinates R (Pi.single 0 1))) ≤
      (2:ℝ≥0∞)^(n+1)*((P.totalDegree : ℝ≥0∞)*volume D) := by
  let U := (fun x => transverseProjection n ((orthogonalCoordinates R).symm x)) ⁻¹' D
  have hU : MeasurableSet U := hD.preimage
    ((transverseProjection n).measurable.comp (orthogonalCoordinates R).symm.continuous.measurable)
  have hh := A.colored_restrict_area_le
    (fun i => visibilityCube (fun j => (z i j:ℝ))) (fun _ => measurableSet_closedBall)
    (fun i => latticeCubeColor (z i))
    (fun i j hij hc => latticeCube_same_color_disjoint (z i) (z j) (fun he => hij (hz he)) hc)
    U hU (fun i x hx => hproj i x hx) (orthogonalCoordinates R (Pi.single 0 1))
  have hb := polynomial_frame_cylinder_budget P hP A R D hD
  have hc : (Fintype.card (Fin (n+1) → Fin 2) : ℝ≥0∞)=(2:ℝ≥0∞)^(n+1) := by simp
  rw [hc] at hh
  exact hh.trans (mul_le_mul le_rfl hb zero_le zero_le)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.DisjointChartAtlas.colored_restrict_area_le
#print axioms KakeyaTwoScale.latticeCube_same_color_disjoint

#print axioms KakeyaTwoScale.polynomial_lattice_projection_budget
