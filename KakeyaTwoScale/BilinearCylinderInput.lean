module
public import KakeyaTwoScale.BrushTubeOverlap
public import KakeyaTwoScale.TubeSliceVolume
public import KakeyaTwoScale.GramRecursion
public import KakeyaTwoScale.MultilinearMass

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Actual two-vector wedge, with no angular lower bound. -/
def pairWedge {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  tupleWedgeVolume (Fin.cons u (fun _ : Fin 1 => v))

/-- Compatibility with the unchanged ordered-tuple wedge in ZahlContract. -/
theorem pairWedge_eq_tuple {d : ℕ} (v : Fin 2 → EuclideanSpace ℝ (Fin d)) :
    pairWedge (v 0) (v 1) = tupleWedgeVolume v := by
  unfold pairWedge
  congr 1
  funext i
  fin_cases i <;> rfl

theorem pairWedge_eq_normal {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖=1) :
    pairWedge u v = ‖normalProjection (Submodule.span ℝ (Set.range (fun _ : Fin 1 => v))) u‖ := by
  rw [pairWedge,tupleWedgeVolume_cons,tupleWedgeVolume_singleton,hv,one_mul]

theorem pairWedge_nonneg {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) :
    0 ≤ pairWedge u v := tupleWedgeVolume_nonneg _

theorem pairWedge_le_one {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖=1) (hv : ‖v‖=1) : pairWedge u v ≤ 1 := by
  rw [pairWedge_eq_normal u v hv,← hu]
  exact (Submodule.span ℝ (Set.range (fun _ : Fin 1 => v)))ᗮ.norm_starProjection_apply_le u

/-- Two actual common points lie in a ball whose radius is inverse to the
wedge. Only positive wedge is used; no quantitative transversality is assumed. -/
theorem capsule_pair_diameter {d : ℕ} (b c u v p x : EuclideanSpace ℝ (Fin d))
    {r : ℝ} (hr : 0<r) (hu : ‖u‖=1) (hv : ‖v‖=1) (hw : 0<pairWedge u v)
    (hp : p ∈ euclideanTube b u r ∩ euclideanTube c v r)
    (hx : x ∈ euclideanTube b u r ∩ euclideanTube c v r) :
    dist x p < 7*r/pairWedge u v := by
  let H := Submodule.span ℝ (Set.range (fun _ : Fin 1 => v))
  let P := normalProjection H
  have hPv : P v = 0 := normalProjection_zero H (Submodule.subset_span ⟨0,rfl⟩)
  have hPn (z) : ‖P z‖ ≤ ‖z‖ := Hᗮ.norm_starProjection_apply_le z
  obtain ⟨t,ht⟩ := tube_two_point_near_line b u p x hp.1 hx.1
  obtain ⟨s,hs⟩ := tube_two_point_near_line c v p x hp.2 hx.2
  have hsmall : ‖P (x-p)‖ ≤ 2*r := by
    have hh := hPn ((x-p)-s • v)
    rw [map_sub,map_smul,hPv,smul_zero,sub_zero] at hh
    exact hh.trans (by simpa [dist_eq_norm] using hs)
  have hterr : ‖P ((x-p)-t • u)‖ ≤ 2*r :=
    (hPn _).trans (by simpa [dist_eq_norm] using ht)
  have htri := norm_sub_le (P (x-p)) (P ((x-p)-t • u))
  have hid : P (x-p)-P ((x-p)-t • u)=t • P u := by simp only [map_sub,map_smul]; abel
  rw [hid,norm_smul,Real.norm_eq_abs] at htri
  have hwid : ‖P u‖=pairWedge u v := (pairWedge_eq_normal u v hv).symm
  rw [hwid] at htri
  have htbound : |t| ≤ 4*r/pairWedge u v := (le_div_iff₀ hw).mpr (by linarith)
  have hdist := norm_le_norm_add_norm_sub (t • u) (x-p)
  rw [norm_sub_rev (t • u)] at hdist
  rw [norm_smul,Real.norm_eq_abs,hu,mul_one] at hdist
  have herr : ‖(x-p)-t • u‖ ≤ 2*r := by simpa [dist_eq_norm] using ht
  have hwl := pairWedge_le_one u v hu hv
  rw [dist_eq_norm]
  apply (lt_div_iff₀ hw).mpr
  have hh := mul_le_mul_of_nonneg_right htbound hw.le
  rw [div_mul_cancel₀ _ hw.ne'] at hh
  have hdistw := mul_le_mul_of_nonneg_right hdist hw.le
  have herrw := mul_le_mul_of_nonneg_right herr hw.le
  nlinarith

/-- Genuine determinant-weighted bilinear overlap, valid for arbitrary
positions and arbitrarily small wedges. The zero-wedge case is included. -/
theorem capsule_pair_weighted_volume {n : ℕ}
    (b c u v : EuclideanSpace ℝ (Fin (n+1))) {r : ℝ}
    (hr : 0<r) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    pairWedge u v * volume.real (euclideanTube b u r ∩ euclideanTube c v r) ≤
      (14*(2*(n+3:ℝ))^n)*r^(n+1) := by
  by_cases hw : pairWedge u v=0
  · rw [hw,zero_mul]; positivity
  have hwp : 0<pairWedge u v := lt_of_le_of_ne (pairWedge_nonneg u v) (Ne.symm hw)
  by_cases hne : (euclideanTube b u r ∩ euclideanTube c v r).Nonempty
  · obtain ⟨p,hp⟩ := hne
    have hs : euclideanTube b u r ∩ euclideanTube c v r ⊆
        euclideanTube b u r ∩ Metric.ball p (7*r/pairWedge u v) := by
      intro x hx
      exact ⟨hx.1,capsule_pair_diameter b c u v p x hr hu hv hwp hp hx⟩
    have hf : volume (euclideanTube b u r ∩ Metric.ball p (7*r/pairWedge u v)) ≠ ⊤ :=
      measure_ne_top_of_subset Set.inter_subset_left (euclideanTube_finite b u r)
    have hh := (measureReal_mono hs hf).trans
      (euclideanTube_inter_ball_volume b u p hr (by positivity) hu)
    have hm := mul_le_mul_of_nonneg_left hh hwp.le
    convert hm using 1
    rw [pow_succ]
    field_simp
    ring
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp only [measureReal_empty,mul_zero]
    positivity

/-- Flat cylinders inherit the pair bound with the same constant. -/
theorem flatCylinder_pair_weighted_volume {n : ℕ}
    (b c u v : EuclideanSpace ℝ (Fin (n+1))) {r : ℝ}
    (hr : 0<r) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    pairWedge u v * volume.real (flatCylinder b u 1 r ∩ flatCylinder c v 1 r) ≤
      (14*(2*(n+3:ℝ))^n)*r^(n+1) := by
  have hs := Set.inter_subset_inter (flatCylinder_subset_unit_capsule b u r r le_rfl)
    (flatCylinder_subset_unit_capsule c v r r le_rfl)
  have hf : volume (euclideanTube b u r ∩ euclideanTube c v r) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_left (euclideanTube_finite b u r)
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hs hf) (pairWedge_nonneg u v)).trans
    (capsule_pair_weighted_volume b c u v hr hu hv)

private theorem pair_indicator_eq {X : Type*} (S T : Set X) (w : ℝ) :
    (fun x => w * S.indicator (fun _ => (1:ℝ)) x * T.indicator (fun _ => (1:ℝ)) x) =
      (S ∩ T).indicator (fun _ => w) := by
  funext x
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;> simp [hs,ht]

/-- Actual determinant-weighted bilinear Kakeya integral for arbitrary finite
families of unit flat cylinders, with no direction separation hypothesis.
The right side is C_n r^(n+1) |A| |B|, the exact bilinear dimensional power. -/
theorem flatCylinder_bilinear_integral {n : ℕ} {I J : Type*}
    (A : Finset I) (B : Finset J)
    (b u : I → EuclideanSpace ℝ (Fin (n+1)))
    (c v : J → EuclideanSpace ℝ (Fin (n+1))) {r : ℝ}
    (hr : 0<r) (hu : ∀ i∈A, ‖u i‖=1) (hv : ∀ j∈B, ‖v j‖=1) :
    (∫ x, ∑ i∈A, ∑ j∈B, pairWedge (u i) (v j) *
      (flatCylinder (b i) (u i) 1 r).indicator (fun _ => (1:ℝ)) x *
      (flatCylinder (c j) (v j) 1 r).indicator (fun _ => (1:ℝ)) x) ≤
      (14*(2*(n+3:ℝ))^n)*r^(n+1)*(A.card:ℝ)*(B.card:ℝ) := by
  let E := fun i j => flatCylinder (b i) (u i) 1 r ∩ flatCylinder (c j) (v j) 1 r
  have hm i (hi : i∈A) j (hj : j∈B) : MeasurableSet (E i j) :=
    (isOpen_flatCylinder _ _ _ _ (hu i hi)).measurableSet.inter
      (isOpen_flatCylinder _ _ _ _ (hv j hj)).measurableSet
  have hf i j : volume (E i j) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_left (flatCylinder_unit_finite _ _ _)
  have hint i (hi : i∈A) j (hj : j∈B) :
      Integrable ((E i j).indicator (fun _ => pairWedge (u i) (v j))) volume :=
    (integrableOn_const (hf i j)).integrable_indicator (hm i hi j hj)
  have hfun : (fun x => ∑ i∈A, ∑ j∈B, pairWedge (u i) (v j) *
      (flatCylinder (b i) (u i) 1 r).indicator (fun _ => (1:ℝ)) x *
      (flatCylinder (c j) (v j) 1 r).indicator (fun _ => (1:ℝ)) x) =
      (fun x => ∑ i∈A, ∑ j∈B, (E i j).indicator (fun _ => pairWedge (u i) (v j)) x) := by
    funext x
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact congrFun (pair_indicator_eq _ _ _) x
  rw [hfun,integral_finsetSum _ (fun i hi => integrable_finsetSum _ (hint i hi))]
  have hinner i (hi : i∈A) :
      (∫ x, ∑ j∈B, (E i j).indicator (fun _ => pairWedge (u i) (v j)) x) ≤
        ∑ j∈B, (14*(2*(n+3:ℝ))^n)*r^(n+1) := by
    rw [integral_finsetSum _ (hint i hi)]
    apply Finset.sum_le_sum
    intro j hj
    rw [integral_indicator_const _ (hm i hi j hj)]
    simpa only [smul_eq_mul,mul_comm] using
      flatCylinder_pair_weighted_volume (b i) (c j) (u i) (v j) hr (hu i hi) (hv j hj)
  calc
    _ ≤ ∑ i∈A, ∑ j∈B, (14*(2*(n+3:ℝ))^n)*r^(n+1) := Finset.sum_le_sum hinner
    _ = _ := by simp; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.capsule_pair_diameter
#print axioms KakeyaTwoScale.capsule_pair_weighted_volume

#print axioms KakeyaTwoScale.flatCylinder_pair_weighted_volume
#print axioms KakeyaTwoScale.flatCylinder_bilinear_integral

#print axioms KakeyaTwoScale.pairWedge_eq_tuple
