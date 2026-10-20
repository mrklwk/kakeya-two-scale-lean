module
public import KakeyaTwoScale.NestedTubeCaptureInduction

@[expose] public section

open Set Metric NormedSpace
noncomputable section
namespace KakeyaTwoScale

/-- Every outer captured point on the common affine line belongs to the
recursive target. It need not belong to the shortened outer working segment. -/
theorem nestedTubeSet_retains_captured_point {n r e : ℕ} (D : ℕ) (B : ℝ)
    (p : TubeRecursionParameter n r e→ℝ) (b v : EuclideanSpace ℝ (Fin (n+1)))
    (starts : Fin r→ℝ) (i : Fin r) (rest : List (Fin r))
    (hB : 0≤B) (hrho : 0<p (Sum.inl .radius)) (hv : 1≤‖v‖)
    (hscale : ∀ j∈i::rest, 0<p (Sum.inl (.length j)) ∧
      p (Sum.inl .radius)≤p (Sum.inl (.length j))/4)
    (hchain : (i::rest).IsChain (fun j k => p (Sum.inl (.length k))≤p (Sum.inl (.length j)) ∧
      p (Sum.inr j)=recursionDilation n B*p (Sum.inl (.length j))/p (Sum.inl (.length k))))
    (hcapture : nestedLineCapture D B (i::rest) p b v starts)
    (t : ℝ) (ht : b+t • v∈thickening (p (Sum.inl .radius))
      (nestedPolynomialZero D p i∩closedBall (nestedCenter p) (B*p (Sum.inl (.length i))))) :
    b+t • v∈nestedTubeSet D B (recursionKappa n) (recursionBeta n) (i::rest) p := by
  have hi := hscale i (by simp)
  have hlocal := captured_point_base_localization (b+t • v) (nestedCenter p)
    (p (Sum.inl .radius)) B (p (Sum.inl (.length i))) (nestedPolynomialZero D p i) hrho hi.2 ht
  cases rest with
  | nil =>
    rw [nestedTubeSet_singleton D B (recursionKappa n) (recursionBeta n) p i hB hrho hi.1]
    exact hlocal
  | cons j rest =>
    obtain ⟨⟨horder,hA⟩,hchain'⟩ := List.isChain_cons_cons.mp hchain
    have hj := hscale j (by simp)
    have hLj := hj.1
    have hk := recursionKappa_pos n
    have hb := recursionBeta_pos n
    have hv0 : v≠0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hv)
    have htail := nestedTubeSet_retains_workingTube D B p b v starts j rest hB hrho hv
      (fun k hk => hscale k (List.mem_cons_of_mem i hk)) hchain'
      (fun k hk => hcapture k (List.mem_cons_of_mem i hk))
    have hmid_j := captured_affine_midpoint_bound b v (nestedCenter p) (starts j)
      (recursionKappa n*p (Sum.inl (.length j))) (p (Sum.inl .radius)) B (p (Sum.inl (.length j)))
      (nestedPolynomialZero D p j) (by positivity) (by linarith [hj.2]) (hcapture j (by simp))
    have hpoint : dist (b+t • v) (nestedCenter p)<(B+1)*p (Sum.inl (.length i)) := by
      have hh := captured_point_dist_lt (nestedPolynomialZero D p i) (nestedCenter p) (b+t • v)
        (p (Sum.inl .radius)) (B*p (Sum.inl (.length i))) ht
      nlinarith [hi.2]
    have hgeom := affine_point_Fat_containment b v (nestedCenter p) t
      (starts j+recursionKappa n*p (Sum.inl (.length j))/2)
      B (p (Sum.inl (.length i))) (p (Sum.inl (.length j)))
      (recursionBeta n*p (Sum.inl .radius)) hv0 hB hj.1 horder (by positivity) hpoint hmid_j
    rw [nestedTubeSet_cons D B (recursionKappa n) (recursionBeta n) p i j rest hrho]
    refine ⟨hlocal.1,?_⟩
    rw [hA]
    exact centeredCylinder_dilate_subset_prescribedFat _ _ _ _ _ _ (norm_normalize hv0) htail hgeom

end KakeyaTwoScale
#print axioms KakeyaTwoScale.nestedTubeSet_retains_captured_point
