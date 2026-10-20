module
public import KakeyaTwoScale.MaximalDeterminantBasis
public import KakeyaTwoScale.AffineEllipsoidArea
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Convex symmetry controls every signed linear combination with l1 budget one. -/
theorem convex_signed_sum_mem {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (K : Set E) (hK : Convex ℝ K)
    (h0 : (0:E) ∈ K) (hneg : ∀ x ∈ K, -x ∈ K)
    (v : ι → E) (hv : ∀ i, v i ∈ K) (a : ι → ℝ) (ha : ∑ i, |a i| ≤ 1) :
    (∑ i, a i • v i) ∈ K := by
  classical
  let w : Option ι → ℝ := fun i => i.elim (1-∑ j, |a j|) (fun j => |a j|)
  let z : Option ι → E := fun i => i.elim 0 (fun j => if 0 ≤ a j then v j else -v j)
  have hw (i) : 0 ≤ w i := by
    cases i with
    | none => exact sub_nonneg.mpr ha
    | some i => exact abs_nonneg _
  have hz (i) : z i ∈ K := by
    cases i with
    | none => exact h0
    | some i =>
      dsimp [z]
      split_ifs
      · exact hv i
      · exact hneg _ (hv i)
  have hs : ∑ i, w i = 1 := by simp [w,Fintype.sum_option]
  have hh := hK.sum_mem (t:=Finset.univ) (fun i _ => hw i) hs (fun i _ => hz i)
  have he : (∑ i, w i • z i) = ∑ i, a i • v i := by
    rw [Fintype.sum_option]
    simp only [w,z,Option.elim_none,Option.elim_some,smul_zero,zero_add]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ a i
    · simp [hi,abs_of_nonneg hi]
    · simp [hi,abs_of_neg (lt_of_not_ge hi),smul_neg,neg_smul]
  rwa [he] at hh

theorem coordinate_l1_le_norm_mul {N : ℕ} (x : Fin N → ℝ) :
    (∑ i, |x i|) ≤ (N:ℝ) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ := by
  calc
    _ ≤ ∑ _i : Fin N, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using
        (PiLp.norm_apply_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N)) i)
    _ = _ := by simp

theorem coordinate_norm_le_l1 {N : ℕ} (x : Fin N → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ ≤ ∑ i, |x i| := by
  have he : (∑ i, EuclideanSpace.single i (x i)) = (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N)) := by
    ext j
    simp
  rw [← he]
  exact (norm_sum_le _ _).trans_eq (by simp [PiLp.norm_single,Real.norm_eq_abs])

/-- Explicit linear ellipsoid comparison with factors N and N^2. The map is
constructed from the maximum-determinant basis, not supplied by the caller. -/
theorem exists_coordinate_ellipsoid_comparison {N : ℕ} (hN : 0 < N)
    (K : Set (Fin N → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hneg : ∀ x ∈ K, -x ∈ K) (ρ : ℝ) (hρ : 0 < ρ)
    (hinner : coordinateEuclideanBall N ρ ⊆ K) :
    ∃ B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ),
      B '' coordinateEuclideanBall N (1/(N:ℝ)) ⊆ K ∧
      K ⊆ B '' {x | ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ ≤ (N:ℝ)} := by
  obtain ⟨b,hb,hcoord⟩ := exists_maximal_determinant_basis K hK ρ hρ hinner
  let B := b.equivFun.symm.toContinuousLinearEquiv
  have h0 : (0 : Fin N → ℝ) ∈ K := hinner (by simpa [coordinateEuclideanBall] using hρ)
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  refine ⟨B,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    change b.equivFun.symm x ∈ K
    rw [Module.Basis.equivFun_symm_apply]
    apply convex_signed_sum_mem K hconv h0 hneg b hb x
    have hnorm : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ < 1/(N:ℝ) := by
      simpa only [coordinateEuclideanBall,mem_ofPred_eq,mem_ball_zero_iff] using hx
    apply (coordinate_l1_le_norm_mul x).trans
    have hh := (lt_div_iff₀ hNr).mp hnorm
    nlinarith
  · intro x hx
    refine ⟨b.equivFun x,?_,by simp [B]⟩
    apply (coordinate_norm_le_l1 _).trans
    calc
      _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => hcoord x hx i)
      _ = _ := by simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.convex_signed_sum_mem
#print axioms KakeyaTwoScale.coordinate_l1_le_norm_mul
#print axioms KakeyaTwoScale.coordinate_norm_le_l1
#print axioms KakeyaTwoScale.exists_coordinate_ellipsoid_comparison
