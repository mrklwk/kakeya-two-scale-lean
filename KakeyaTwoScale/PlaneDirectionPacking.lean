module
public import KakeyaTwoScale.SpherePacking
public import KakeyaTwoScale.EuclideanTubeSource

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Normalize the tangential projection without assuming that the direction
already lies in the plane. The hypothesis excludes the zero projection. -/
theorem tangent_unit_approx {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (H : Submodule ℝ X) [H.HasOrthogonalProjection] (u : X) (e : ℝ)
    (hu : ‖u‖=1) (he : ‖normalProjection H u‖ ≤ e) (heone : e < 1) :
    ∃ v : H, ‖v‖=1 ∧ dist u (v:X) ≤ 2*e := by
  let q : H := ⟨H.starProjection u,H.starProjection_apply_mem u⟩
  have hn : 0 < ‖q‖ := by
    have hid : u=H.starProjection u+normalProjection H u := by
      rw [normalProjection,Submodule.starProjection_orthogonal_val]; abel
    have hh := norm_add_le (H.starProjection u) (normalProjection H u)
    rw [← hid,hu] at hh
    change 0 < ‖H.starProjection u‖
    linarith
  let v := NormedSpace.normalize q
  have hv : ‖v‖=1 := NormedSpace.norm_normalize_eq_one_iff.mpr (norm_pos_iff.mp hn)
  refine ⟨v,hv,?_⟩
  have hid : ‖q‖ • (v:X) = H.starProjection u := by
    have hh := congrArg (fun z : H => (z:X)) (NormedSpace.norm_smul_normalize q)
    exact hh
  have hnear : dist u (‖q‖ • (v:X)) ≤ e := by
    rw [hid,dist_eq_norm]
    simpa [normalProjection,Submodule.starProjection_orthogonal_val] using he
  have hh := direction_of_near_ray u (v:X) ‖q‖ e 1 hv hn.le (by norm_num)
    (by rw [hu]) hnear
  simpa [hu] using hh

/-- Projective separation survives independent choices of orientation. -/
theorem projective_dist_signed {X : Type*} [NormedAddCommGroup X]
    (u v : X) (P Q : Prop) [Decidable P] [Decidable Q] (r : ℝ)
    (hp : r ≤ dist u v) (hn : r ≤ dist u (-v)) :
    r ≤ dist (if P then u else -u) (if Q then v else -v) := by
  have hneg : dist (-u) v=dist u (-v) := by
    rw [dist_eq_norm,dist_eq_norm]
    have he : -u-v= -(u-(-v)) := by abel
    rw [he,norm_neg]
  split_ifs
  · exact hp
  · exact hn
  · rwa [hneg]
  · simpa using hp

/-- Directions in a small neighborhood of a (k+1)-plane have packing power k.
The constant is uniform over the plane, scale and finite family. -/
theorem near_plane_direction_packing (d k : ℕ) (C : ℝ) (_hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin d))) [H.HasOrthogonalProjection],
      Module.finrank ℝ H=k+1 → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ {J : Type*} (G : Finset J) (u : J → EuclideanSpace ℝ (Fin d)),
      (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, ‖normalProjection H (u j)‖ ≤ C*r) →
      (∀ j ∈ G, ∀ l ∈ G, j ≠ l → r ≤ dist (u j) (u l) ∧ r ≤ dist (u j) (-u l)) →
      (G.card:ℝ)*r^k ≤ K := by
  obtain ⟨N0,hN0⟩ := uniform_local_packing (X:=EuclideanSpace ℝ (Fin d)) (2*C)
  obtain ⟨N1,hN1⟩ := uniform_local_packing (X:=EuclideanSpace ℝ (Fin d)) (2*C+1)
  let A : ℝ := 2*(k+1:ℝ)*2^k*3^k
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨(N0:ℝ)+(N1:ℝ)*A+1,by positivity,?_⟩
  intro H instH hdim r hr hrone J G u hu hnear hsep
  by_cases hlarge : 1/2 ≤ C*r
  · have hc : G.card ≤ N0 := hN0 r hr 0 G u
      (fun j hj => by rw [dist_zero_right,hu j hj]; nlinarith) (fun j hj l hl hne => (hsep j hj l hl hne).1)
    have hp : r^k ≤ (1:ℝ) := pow_le_one₀ hr.le hrone
    have hh := mul_le_mul (show (G.card:ℝ) ≤ N0 by exact_mod_cast hc) hp (pow_nonneg hr.le _) (Nat.cast_nonneg _)
    nlinarith [show 0 ≤ (N1:ℝ)*A by positivity]
  by_cases hG : G.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hG]
    positivity
  have hvex : ∀ j ∈ G, ∃ v : H, ‖v‖=1 ∧ dist (u j) (v:EuclideanSpace ℝ (Fin d)) ≤ 2*(C*r) := by
    intro j hj
    exact tangent_unit_approx H (u j) (C*r) (hu j hj) (hnear j hj) (by linarith)
  let v := fun j => if hj : j ∈ G then (hvex j hj).choose else (0:H)
  have hv (j) (hj : j ∈ G) : ‖v j‖=1 ∧ dist (u j) (v j:EuclideanSpace ℝ (Fin d)) ≤ 2*(C*r) := by
    dsimp [v]; rw [dite_eq_left hj]; exact (hvex j hj).choose_spec
  obtain ⟨net,assign,hnet,hnetsep,hassign⟩ := finite_projective_net_assignment G hG v r hr
  let oriented := fun j => if dist (v j) (v (assign j)) < r then u j else -u j
  have horientsep : ∀ j ∈ G, ∀ l ∈ G, j ≠ l → r ≤ dist (oriented j) (oriented l) := by
    intro j hj l hl hjl
    exact projective_dist_signed _ _ _ _ r (hsep j hj l hl hjl).1 (hsep j hj l hl hjl).2
  have hclose : ∀ j ∈ G, dist (oriented j) (v (assign j):EuclideanSpace ℝ (Fin d)) ≤ (2*C+1)*r := by
    intro j hj
    have happrox := (hv j hj).2
    have hnetclose := (hassign j hj).2
    dsimp [oriented]
    split_ifs with hp
    · have hh := dist_triangle (u j) (v j:EuclideanSpace ℝ (Fin d)) (v (assign j):EuclideanSpace ℝ (Fin d))
      have hp' : dist (v j:EuclideanSpace ℝ (Fin d)) (v (assign j):EuclideanSpace ℝ (Fin d)) < r := hp
      nlinarith
    · have hn := hnetclose.resolve_left hp
      have hh := dist_triangle (-u j) (-(v j:EuclideanSpace ℝ (Fin d))) (v (assign j):EuclideanSpace ℝ (Fin d))
      have hn' : dist (-(v j:EuclideanSpace ℝ (Fin d))) (v (assign j):EuclideanSpace ℝ (Fin d)) < r := by
        rw [dist_eq_norm,show -(v j:EuclideanSpace ℝ (Fin d))-(v (assign j):EuclideanSpace ℝ (Fin d)) =
          -((v j:EuclideanSpace ℝ (Fin d))+(v (assign j):EuclideanSpace ℝ (Fin d))) by abel,norm_neg]
        simpa [dist_eq_norm,sub_neg_eq_add] using hn
      rw [dist_neg_neg] at hh
      nlinarith
  have hfib : ∀ l ∈ net, (G.filter (fun j => assign j=l)).card ≤ N1 := by
    intro l hl
    apply hN1 r hr (v l:EuclideanSpace ℝ (Fin d)) _ oriented
    · intro j hj
      obtain ⟨hj,hjl⟩ := Finset.mem_filter.mp hj
      have hh := hclose j hj
      rwa [hjl] at hh
    · intro j hj m hm hjm
      exact horientsep j (Finset.mem_filter.mp hj).1 m (Finset.mem_filter.mp hm).1 hjm
  have hcard : G.card ≤ net.card*N1 := by
    calc
      _ = ∑ l ∈ net, (G.filter (fun j => assign j=l)).card := Finset.card_eq_sum_card_fiberwise (fun j hj => (hassign j hj).1)
      _ ≤ ∑ _l ∈ net, N1 := Finset.sum_le_sum hfib
      _ = _ := by simp
  have hnetcard := sphere_packing_bound k hdim net v hr hrone (fun j hj => (hv j (hnet hj)).1)
    (fun j hj l hl hjl => (hnetsep j hj l hl hjl).1)
  have hc : (G.card:ℝ) ≤ (net.card:ℝ)*N1 := by exact_mod_cast hcard
  have hh := mul_le_mul_of_nonneg_right hc (pow_nonneg hr.le k)
  have hn := mul_le_mul_of_nonneg_left hnetcard (Nat.cast_nonneg N1 : (0:ℝ) ≤ N1)
  change _ ≤ (N0:ℝ)+(N1:ℝ)*A+1
  change (net.card:ℝ)*r^k ≤ A at hnetcard
  nlinarith [Nat.cast_nonneg N0 (α:=ℝ)]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tangent_unit_approx
#print axioms KakeyaTwoScale.projective_dist_signed
#print axioms KakeyaTwoScale.near_plane_direction_packing
