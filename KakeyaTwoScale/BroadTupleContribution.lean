module
public import KakeyaTwoScale.ZahlContract
public import KakeyaTwoScale.PlaneAngle

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- An actual finite set of incident ordered tuples contributes its full
wedge-weighted cardinality to the original multilinear sum. -/
theorem multilinear_lower_of_good_tuples {n N k : ℕ}
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B v : ℝ)
    (hB : 0<B) (hv : 0≤v) (x : EuclideanSpace ℝ (Fin n))
    (good : Finset (Fin k → Fin N))
    (hincident : ∀ f∈good, ∀ i, x∈T (f i))
    (hwedge : ∀ f∈good, v≤tupleWedgeVolume (fun i => u (f i))) :
    ((good.card:ℝ)*v^((k:ℝ)/B))^((1:ℝ)/k) ≤
      multilinearKakeyaFunction k u T B x := by
  unfold multilinearKakeyaFunction
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  let term := fun f : Fin k → Fin N =>
    (tupleWedgeVolume (fun i => u (f i)))^((k:ℝ)/B) *
      ∏ i : Fin k, (T (f i)).indicator (fun _ => (1:ℝ)) x
  have hnonneg : ∀ f, 0≤term f := by
    intro f
    exact mul_nonneg (Real.rpow_nonneg (tupleWedgeVolume_nonneg _) _)
      (Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => by norm_num) x)
  calc
    _ = ∑ _f∈good,v^((k:ℝ)/B) := by simp
    _ ≤ ∑ f∈good,term f := by
      apply Finset.sum_le_sum
      intro f hf
      have hi : (∏ i : Fin k,(T (f i)).indicator (fun _ => (1:ℝ)) x)=1 := by
        apply Finset.prod_eq_one
        intro i _
        exact Set.indicator_of_mem (hincident f hf i) _
      dsimp [term]
      rw [hi,mul_one]
      exact Real.rpow_le_rpow hv (hwedge f hf) (by positivity)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
      (fun f _ _ => hnonneg f)

/-- A proved tuple-count lower bound immediately yields the source's
multiplicity lower bound, without changing the ambient tube family. -/
theorem multilinear_lower_of_tuple_count {n N k : ℕ}
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B v c μ : ℝ)
    (hB : 0<B) (hv : 0≤v) (hc : 0≤c) (hμ : 0≤μ)
    (x : EuclideanSpace ℝ (Fin n)) (good : Finset (Fin k → Fin N))
    (hincident : ∀ f∈good, ∀ i, x∈T (f i))
    (hwedge : ∀ f∈good, v≤tupleWedgeVolume (fun i => u (f i)))
    (hcount : c*μ^k≤(good.card:ℝ)) :
    (c*v^((k:ℝ)/B)*μ^k)^((1:ℝ)/k) ≤ multilinearKakeyaFunction k u T B x := by
  apply le_trans _ (multilinear_lower_of_good_tuples u T B v hB hv x good hincident hwedge)
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hv ((k:ℝ)/B))]

theorem tuple_lower_bound_factorization {k : ℕ} (hk : 0<k)
    {B v c μ : ℝ} (hB : 0<B) (hv : 0≤v) (hc : 0≤c) (hμ : 0≤μ) :
    (c*v^((k:ℝ)/B)*μ^k)^((1:ℝ)/k) = c^((1:ℝ)/k)*v^(1/B)*μ := by
  rw [Real.mul_rpow (by positivity) (pow_nonneg hμ k),
    Real.mul_rpow hc (Real.rpow_nonneg hv _),← Real.rpow_mul hv]
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hexp : ((k:ℝ)/B)*(1/k)=1/B := by field_simp
  rw [hexp,one_div,Real.pow_rpow_inv_natCast hμ (Nat.ne_of_gt hk)]

/-- The actual outside-plane choices used at one greedy step: their count
exceeds half the original incident family, and their normal speed is large. -/
theorem broad_plane_extension_choices {n N : ℕ}
    (G : Finset (Fin N)) (u : Fin N → EuclideanSpace ℝ (Fin n))
    (H : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (ρ : ℝ)
    (hu : ∀ j∈G, ‖u j‖=1)
    (hbroad : (((G.filter fun j => planeAngle H (u j)≤ρ).card):ℝ)<(G.card:ℝ)/2) :
    ∃ outside : Finset (Fin N), outside⊆G ∧
      (G.card:ℝ)/2<(outside.card:ℝ) ∧
      (∀ j∈outside, ρ<planeAngle H (u j) ∧
        (2/Real.pi)*ρ<‖normalProjection H (u j)‖) := by
  let outside := G.filter fun j => ¬planeAngle H (u j)≤ρ
  have hcard := Finset.card_filter_add_card_filter_not (s:=G) (fun j => planeAngle H (u j)≤ρ)
  have hcard' : (((G.filter fun j => planeAngle H (u j)≤ρ).card):ℝ)+(outside.card:ℝ)=G.card := by
    exact_mod_cast hcard
  refine ⟨outside,Finset.filter_subset _ _,by linarith,?_⟩
  intro j hj
  obtain ⟨hjG,hjout⟩ := Finset.mem_filter.mp hj
  have hang := lt_of_not_ge hjout
  refine ⟨hang,?_⟩
  exact (mul_lt_mul_of_pos_left hang (by positivity)).trans_le
    (planeAngle_speed_bounds H (u j) (hu j hjG)).1

end KakeyaTwoScale
#print axioms KakeyaTwoScale.multilinear_lower_of_good_tuples
#print axioms KakeyaTwoScale.multilinear_lower_of_tuple_count

#print axioms KakeyaTwoScale.tuple_lower_bound_factorization
#print axioms KakeyaTwoScale.broad_plane_extension_choices
