module
public import KakeyaTwoScale.CentralCoordinatePaths

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- A finite sequence going from strictly positive to nonpositive crosses an edge.
Repeated vertices and zeros at intermediate vertices are included. -/
theorem finite_sign_crossing (a : ℕ → ℝ) (N : ℕ) (h0 : 0 < a 0) (hN : a N ≤ 0) :
    ∃ j < N, 0 < a j ∧ a (j+1) ≤ 0 := by
  induction N with
  | zero => linarith
  | succ N ih =>
    by_cases h : 0 < a N
    · exact ⟨N,Nat.lt_succ_self N,h,hN⟩
    · obtain ⟨j,hj,hp,hn⟩ := ih (le_of_not_gt h)
      exact ⟨j,Nat.lt_succ_of_lt hj,hp,hn⟩

/-- IVT on a single straight segment, with its actual parameter retained. -/
theorem exists_segment_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : Continuous f) (a b : E) (ha : 0 ≤ f a) (hb : f b ≤ 0) :
    ∃ t ∈ Icc (0:ℝ) 1, f ((1-t) • a+t • b)=0 := by
  have hc : Continuous (fun t : ℝ => f ((1-t) • a+t • b)) :=
    hf.comp (((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const))
  have hm : (0:ℝ) ∈ Icc (f (((1:ℝ)-1) • a+(1:ℝ) • b)) (f (((1:ℝ)-0) • a+(0:ℝ) • b)) := by
    simpa using (show 0 ∈ Icc (f b) (f a) from ⟨hb,ha⟩)
  exact intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hc.continuousOn hm

/-- Positive-to-nonpositive hub paths force a zero on a coordinate line inside
our original ball; no containing-box replacement occurs in this statement. -/
theorem coordinate_path_zero {N : ℕ}
    (f : EuclideanSpace ℝ (Fin N) → ℝ) (hf : Continuous f)
    (x z : EuclideanSpace ℝ (Fin N)) (hbudget : ‖x‖^2+‖z‖^2 < 1)
    (hx : 0 < f x) (hz : f z ≤ 0) :
    ∃ j : Fin N, ∃ w ∈ ball (0 : EuclideanSpace ℝ (Fin N)) 1,
      f w=0 ∧ ∀ i : Fin N, i ≠ j → w i = coordinateHybrid x z j.val i := by
  obtain ⟨j,hj,ha,hb⟩ := finite_sign_crossing (fun k => f (coordinateHybrid x z k)) N
    (by simpa using hx) (by simpa using hz)
  let jj : Fin N := ⟨j,hj⟩
  obtain ⟨t,ht,hzero⟩ := exists_segment_zero f hf
    (coordinateHybrid x z j) (coordinateHybrid x z (j+1)) ha.le hb
  refine ⟨jj,_,coordinateHybrid_segment_mem_ball x z hbudget jj t ht,hzero,?_⟩
  intro i hij
  change (1-t)*coordinateHybrid x z j i+t*coordinateHybrid x z (j+1) i = _
  rw [coordinateHybrid_succ_apply x z jj i hij]
  ring

/-- Opposite signs force a crossing on one of the two paths through any safe hub. -/
theorem two_coordinate_paths_zero {N : ℕ}
    (f : EuclideanSpace ℝ (Fin N) → ℝ) (hf : Continuous f)
    (x y z : EuclideanSpace ℝ (Fin N))
    (hxz : ‖x‖^2+‖z‖^2 < 1) (hyz : ‖y‖^2+‖z‖^2 < 1)
    (hx : 0 < f x) (hy : f y < 0) :
    ∃ j : Fin N, ∃ w ∈ ball (0 : EuclideanSpace ℝ (Fin N)) 1,
      f w=0 ∧ ((∀ i : Fin N, i ≠ j → w i = coordinateHybrid x z j.val i) ∨
        (∀ i : Fin N, i ≠ j → w i = coordinateHybrid y z j.val i)) := by
  by_cases hz : f z ≤ 0
  · obtain ⟨j,w,hw,hf0,he⟩ := coordinate_path_zero f hf x z hxz hx hz
    exact ⟨j,w,hw,hf0,Or.inl he⟩
  · obtain ⟨j,w,hw,hf0,he⟩ := coordinate_path_zero (fun v => -f v) hf.neg y z hyz
      (by linarith) (by linarith)
    exact ⟨j,w,hw,neg_eq_zero.mp hf0,Or.inr he⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_sign_crossing
#print axioms KakeyaTwoScale.exists_segment_zero
#print axioms KakeyaTwoScale.coordinate_path_zero
#print axioms KakeyaTwoScale.two_coordinate_paths_zero
