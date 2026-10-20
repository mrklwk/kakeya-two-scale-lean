module
public import KakeyaTwoScale.UnitWedgeBound
public import KakeyaTwoScale.TinyWedgePointwise
public import Mathlib.Analysis.MeanInequalitiesPow

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical
set_option maxHeartbeats 400000

def dyadicWeightCut (J : ℕ) : ℝ := ((2:ℝ)^J)⁻¹

def dyadicWeightTailSum {ι : Type*} (S : Finset ι) (w f : ι → ℝ) (J : ℕ) : ℝ :=
  ∑ i ∈ S.filter (fun i => w i ≤ dyadicWeightCut J), f i

def dyadicWeightBandSum {ι : Type*} (S : Finset ι) (w f : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ S.filter (fun i => dyadicWeightCut (j+1) < w i ∧ w i ≤ dyadicWeightCut j), f i

theorem dyadicWeightCut_succ_le (J : ℕ) : dyadicWeightCut (J+1) ≤ dyadicWeightCut J := by
  unfold dyadicWeightCut
  apply (inv_le_inv₀ (by positivity) (by positivity)).2
  rw [pow_succ]
  have h := pow_pos (by norm_num : (0:ℝ)<2) J
  linarith

/-- Exact disjoint tail split; the lower equality belongs to the tail. -/
theorem dyadicWeightTailSum_split {ι : Type*} (S : Finset ι) (w f : ι → ℝ) (J : ℕ) :
    dyadicWeightTailSum S w f J =
      dyadicWeightTailSum S w f (J+1)+dyadicWeightBandSum S w f J := by
  unfold dyadicWeightTailSum dyadicWeightBandSum
  simp only [Finset.sum_filter]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have h := dyadicWeightCut_succ_le J
  by_cases hlow : w i ≤ dyadicWeightCut (J+1)
  · have hu := hlow.trans h
    simp [hlow,hu,not_lt_of_ge hlow]
  · have hl : dyadicWeightCut (J+1)<w i := lt_of_not_ge hlow
    by_cases hu : w i ≤ dyadicWeightCut J <;> simp [hlow,hl,hu]

/-- A complete finite decomposition, uniform in arbitrarily small positive
weights. Zero weights and the cutoff equality stay in the tail. -/
theorem finite_dyadic_weight_decomposition {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ S, w i ≤ 1) (J : ℕ) :
    ∑ i ∈ S, f i = dyadicWeightTailSum S w f J+
      ∑ j ∈ Finset.range J, dyadicWeightBandSum S w f j := by
  induction J with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,add_zero]
    unfold dyadicWeightTailSum
    have hfilter : S.filter (fun i => w i ≤ dyadicWeightCut 0)=S := by
      apply Finset.filter_eq_self.mpr
      intro i hi
      simpa [dyadicWeightCut] using hw i hi
    rw [hfilter]
  | succ J ih =>
    rw [Finset.sum_range_succ,ih,dyadicWeightTailSum_split S w f J]
    ring

/-- Concave powers recombine bands by subadditivity, even below exponent one. -/
theorem finite_nonneg_rpow_sum_le {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) {beta : ℝ} (hb : 0<beta) (hb1 : beta ≤ 1) :
    (∑ i ∈ S, f i)^beta ≤ ∑ i ∈ S, (f i)^beta := by
  induction S using Finset.induction_on with
  | empty => simp [Real.zero_rpow hb.ne']
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    have hi0 := hf i (Finset.mem_insert_self _ _)
    have hS : ∀ j ∈ S, 0 ≤ f j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    exact (Real.rpow_add_le_add_rpow hi0 (Finset.sum_nonneg hS) hb.le hb1).trans
      (add_le_add le_rfl (ih hS))

/-- The full finite band decomposition recombines at the target concave
power without assuming a norm triangle inequality below exponent one. -/
theorem finite_dyadic_weight_rpow_le {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ S, w i ≤ 1) (hf : ∀ i ∈ S, 0 ≤ f i)
    (J : ℕ) {beta : ℝ} (hb : 0<beta) (hb1 : beta ≤ 1) :
    (∑ i ∈ S, f i)^beta ≤ (dyadicWeightTailSum S w f J)^beta+
      ∑ j ∈ Finset.range J, (dyadicWeightBandSum S w f j)^beta := by
  have ht : 0 ≤ dyadicWeightTailSum S w f J :=
    Finset.sum_nonneg (fun i hi => hf i (Finset.mem_filter.mp hi).1)
  have hband (j : ℕ) : 0 ≤ dyadicWeightBandSum S w f j :=
    Finset.sum_nonneg (fun i hi => hf i (Finset.mem_filter.mp hi).1)
  rw [finite_dyadic_weight_decomposition S w f hw J]
  exact (Real.rpow_add_le_add_rpow ht (Finset.sum_nonneg (fun j _ => hband j)) hb.le hb1).trans
    (add_le_add le_rfl (finite_nonneg_rpow_sum_le (Finset.range J) _ (fun j _ => hband j) hb hb1))

/-- Direct instantiation on literal original ordered tube tuples. -/
theorem original_wedge_dyadic_decomposition {n N k : ℕ}
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (hu : ∀ i, ‖u i‖=1)
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B : ℝ) (x) (J : ℕ) :
    (∑ f : Fin k → Fin N, (tupleWedgeVolume (fun i => u (f i)))^((k:ℝ)/B)*
      ∏ i, (T (f i)).indicator (fun _ => (1:ℝ)) x) =
      tinyWedgeSum k u T B (dyadicWeightCut J) x+
      ∑ j ∈ Finset.range J, dyadicWeightBandSum Finset.univ
        (fun f : Fin k → Fin N => tupleWedgeVolume (fun i => u (f i)))
        (fun f => (tupleWedgeVolume (fun i => u (f i)))^((k:ℝ)/B)*
          ∏ i, (T (f i)).indicator (fun _ => (1:ℝ)) x) j := by
  let w : (Fin k → Fin N) → ℝ := fun f => tupleWedgeVolume (fun i => u (f i))
  let a : (Fin k → Fin N) → ℝ := fun f => (w f)^((k:ℝ)/B)*
    ∏ i, (T (f i)).indicator (fun _ => (1:ℝ)) x
  have hw : ∀ f ∈ (Finset.univ : Finset (Fin k → Fin N)), w f ≤ 1 := by
    intro f _
    exact tupleWedgeVolume_le_one (n:=n) (k:=k) (fun i => u (f i)) (fun i => hu (f i))
  have h := finite_dyadic_weight_decomposition Finset.univ w a hw J
  exact h

/-- The fixed J=d*q cutoff is exactly the d-th power of the dyadic scale. -/
theorem dyadicWeightCut_mul (d q : ℕ) :
    dyadicWeightCut (d*q) = (dyadicWeightCut q)^d := by
  simp only [dyadicWeightCut, ←inv_pow, ←pow_mul, Nat.mul_comm d q]

/-- Concave recombination on the same literal original ordered tuple sum. -/
theorem original_wedge_dyadic_rpow_le {n N k : ℕ}
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (hu : ∀ i, ‖u i‖=1)
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B : ℝ) (x) (J : ℕ)
    {beta : ℝ} (hb : 0<beta) (hb1 : beta ≤ 1) :
    (∑ f : Fin k → Fin N, (tupleWedgeVolume (fun i => u (f i)))^((k:ℝ)/B)*
      ∏ i, (T (f i)).indicator (fun _ => (1:ℝ)) x)^beta ≤
      (tinyWedgeSum k u T B (dyadicWeightCut J) x)^beta+
      ∑ j ∈ Finset.range J, (dyadicWeightBandSum Finset.univ
        (fun f : Fin k → Fin N => tupleWedgeVolume (fun i => u (f i)))
        (fun f => (tupleWedgeVolume (fun i => u (f i)))^((k:ℝ)/B)*
          ∏ i, (T (f i)).indicator (fun _ => (1:ℝ)) x) j)^beta := by
  let w : (Fin k → Fin N) → ℝ := fun f => tupleWedgeVolume (fun i => u (f i))
  let a : (Fin k → Fin N) → ℝ := fun f => (w f)^((k:ℝ)/B)*
    ∏ i, (T (f i)).indicator (fun _ => (1:ℝ)) x
  have hw : ∀ f ∈ (Finset.univ : Finset (Fin k → Fin N)), w f ≤ 1 := by
    intro f _
    exact tupleWedgeVolume_le_one (n:=n) (k:=k) (fun i => u (f i)) (fun i => hu (f i))
  have ha : ∀ f ∈ (Finset.univ : Finset (Fin k → Fin N)), 0 ≤ a f := by
    intro f _
    exact mul_nonneg (Real.rpow_nonneg (tupleWedgeVolume_nonneg _) _)
      (Finset.prod_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => by norm_num) x))
  exact finite_dyadic_weight_rpow_le Finset.univ w a hw ha J hb hb1

end KakeyaTwoScale
#print axioms KakeyaTwoScale.dyadicWeightTailSum_split
#print axioms KakeyaTwoScale.finite_dyadic_weight_decomposition
#print axioms KakeyaTwoScale.finite_nonneg_rpow_sum_le
#print axioms KakeyaTwoScale.original_wedge_dyadic_decomposition

#print axioms KakeyaTwoScale.finite_dyadic_weight_rpow_le

#print axioms KakeyaTwoScale.dyadicWeightCut_mul
#print axioms KakeyaTwoScale.original_wedge_dyadic_rpow_le
