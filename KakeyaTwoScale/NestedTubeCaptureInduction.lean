module
public import KakeyaTwoScale.NestedTubeSetGeometry
public import KakeyaTwoScale.CapturedTubeLocalization
public import KakeyaTwoScale.AffineFatContainment

@[expose] public section

open Set Metric NormedSpace
noncomputable section
namespace KakeyaTwoScale

/-- Exact common-line capture data, with one intercept/vector for the whole
positive prefix and individually witnessed capture intervals. -/
def nestedLineCapture {n r e : ℕ} (D : ℕ) (B : ℝ) (levels : List (Fin r))
    (p : TubeRecursionParameter n r e→ℝ) (b v : EuclideanSpace ℝ (Fin (n+1)))
    (starts : Fin r→ℝ) : Prop :=
  ∀ i∈levels, ∀ t∈Icc (starts i) (starts i+recursionKappa n*p (Sum.inl (.length i))),
    b+t • v∈thickening (p (Sum.inl .radius))
      (nestedPolynomialZero D p i∩closedBall (nestedCenter p) (B*p (Sum.inl (.length i))))

/-- Each actual captured working tube enters the recursively constructed set.
This proves retention geometrically, without assuming a recursive containment. -/
theorem nestedTubeSet_retains_workingTube {n r e : ℕ} (D : ℕ) (B : ℝ)
    (p : TubeRecursionParameter n r e→ℝ) (b v : EuclideanSpace ℝ (Fin (n+1)))
    (starts : Fin r→ℝ) (i : Fin r) (rest : List (Fin r))
    (hB : 0≤B) (hrho : 0<p (Sum.inl .radius)) (hv : 1≤‖v‖)
    (hscale : ∀ j∈i::rest, 0<p (Sum.inl (.length j)) ∧
      p (Sum.inl .radius)≤p (Sum.inl (.length j))/4)
    (hchain : (i::rest).IsChain (fun j k => p (Sum.inl (.length k))≤p (Sum.inl (.length j)) ∧
      p (Sum.inr j)=recursionDilation n B*p (Sum.inl (.length j))/p (Sum.inl (.length k))))
    (hcapture : nestedLineCapture D B (i::rest) p b v starts) :
    centeredCylinder (b+(starts i+recursionKappa n*p (Sum.inl (.length i))/2) • v)
      (normalize v) (recursionKappa n*p (Sum.inl (.length i))) (recursionBeta n*p (Sum.inl .radius)) ⊆
      nestedTubeSet D B (recursionKappa n) (recursionBeta n) (i::rest) p := by
  have hk := recursionKappa_pos n
  have hb := recursionBeta_pos n
  have hv0 : v≠0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hv)
  have hw : recursionBeta n*p (Sum.inl .radius)≤p (Sum.inl .radius) :=
    mul_le_of_le_one_left hrho.le (recursionBeta_le_one n)
  induction rest generalizing i with
  | nil =>
    have hi := hscale i (by simp)
    have hLi := hi.1
    rw [nestedTubeSet_singleton D B (recursionKappa n) (recursionBeta n) p i hB hrho hi.1]
    exact captured_centeredTube_localization _ _ _ _ _ _ B _ _ hrho hw hi.2
      (captured_working_axis b v (starts i) _ _ _ (by positivity) hv (hcapture i (by simp)))
  | cons j rest ih =>
    obtain ⟨⟨horder,hA⟩,hchain'⟩ := List.isChain_cons_cons.mp hchain
    have hi := hscale i (by simp)
    have hLi := hi.1
    have hj := hscale j (by simp)
    have hLj := hj.1
    have htail := ih j (fun k hk => hscale k (List.mem_cons_of_mem i hk)) hchain'
      (fun k hk => hcapture k (List.mem_cons_of_mem i hk))
    have hmid_i := captured_affine_midpoint_bound b v (nestedCenter p) (starts i)
      (recursionKappa n*p (Sum.inl (.length i))) (p (Sum.inl .radius)) B (p (Sum.inl (.length i)))
      (nestedPolynomialZero D p i) (by positivity) (by linarith) (hcapture i (by simp))
    have hmid_j := captured_affine_midpoint_bound b v (nestedCenter p) (starts j)
      (recursionKappa n*p (Sum.inl (.length j))) (p (Sum.inl .radius)) B (p (Sum.inl (.length j)))
      (nestedPolynomialZero D p j) (by positivity) (by linarith) (hcapture j (by simp))
    have hgeom := affine_workingTube_Fat_containment b v (nestedCenter p)
      (starts i+recursionKappa n*p (Sum.inl (.length i))/2)
      (starts j+recursionKappa n*p (Sum.inl (.length j))/2)
      B (p (Sum.inl (.length i))) (p (Sum.inl (.length j)))
      (recursionBeta n*p (Sum.inl .radius)) hv0 hB hj.1 horder (by positivity) hmid_i hmid_j
    have hlocal := captured_centeredTube_localization _ _ (nestedCenter p)
      (recursionKappa n*p (Sum.inl (.length i))) (recursionBeta n*p (Sum.inl .radius))
      (p (Sum.inl .radius)) B (p (Sum.inl (.length i))) (nestedPolynomialZero D p i) hrho hw hi.2
      (captured_working_axis b v (starts i) _ _ _ (by positivity) hv (hcapture i (by simp)))
    rw [nestedTubeSet_cons D B (recursionKappa n) (recursionBeta n) p i j rest hrho]
    intro x hx
    refine ⟨(hlocal hx).1,?_⟩
    rw [hA]
    exact centeredCylinder_dilate_subset_prescribedFat _ _ _ _ _ _ (norm_normalize hv0) htail (hgeom hx)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.nestedTubeSet_retains_workingTube
