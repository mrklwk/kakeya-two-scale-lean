module
public import KakeyaTwoScale.LocalPacking
public import KakeyaTwoScale.TubeShortening
public import KakeyaTwoScale.WeightedBrushCounting

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A point away from the origin and close to a unit ray determines its
normalized direction, with an explicit error. -/
theorem direction_of_near_ray (x a : X) (t r d : ℝ) (ha : ‖a‖ = 1)
    (ht : 0 ≤ t) (hd : 0 < d) (hx : d ≤ ‖x‖) (hnear : dist x (t • a) ≤ r) :
    dist (‖x‖⁻¹ • x) a ≤ 2*r/d := by
  have hxp : 0 < ‖x‖ := hd.trans_le hx
  have hr : 0 ≤ r := dist_nonneg.trans hnear
  have hnorm : |t-‖x‖| ≤ r := by
    have hh := abs_norm_sub_norm_le (t • a) x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, ha, mul_one] at hh
    have hn : ‖t • a-x‖ ≤ r := by simpa [dist_eq_norm, norm_sub_rev] using hnear
    exact hh.trans hn
  have hsame : dist (t • a) (‖x‖ • a) ≤ r := by
    rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, ha, mul_one]
    exact hnorm
  have hdist : dist x (‖x‖ • a) ≤ 2*r := by
    have hh := dist_triangle x (t • a) (‖x‖ • a)
    linarith
  calc
    _ = dist (‖x‖⁻¹ • x) (‖x‖⁻¹ • (‖x‖ • a)) := by
      rw [smul_smul, inv_mul_cancel₀ hxp.ne', one_smul]
    _ = ‖x‖⁻¹ * dist x (‖x‖ • a) := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos hxp]
    _ ≤ ‖x‖⁻¹*(2*r) := mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = 2*r/‖x‖ := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hd hx

variable [ProperSpace X]

/-- Uniform bounded overlap for separated oriented rays away from their common
origin. K is fixed before all scales, points and families. -/
theorem uniform_separated_ray_overlap (K : ℝ) (_hK : 0 ≤ K) :
    ∃ B : ℕ, ∀ (epsilon d : ℝ), 0 < epsilon → 0 < d → ∀ (x : X), d ≤ ‖x‖ →
    ∀ {J : Type*} (family : Finset J) (a : J → X) (t : J → ℝ),
    (∀ j ∈ family, ‖a j‖ = 1) → (∀ j ∈ family, 0 ≤ t j) →
    (∀ j ∈ family, dist x ((t j) • a j) ≤ K*epsilon*d) →
    (∀ j ∈ family, ∀ k ∈ family, j ≠ k → epsilon ≤ dist (a j) (a k)) → family.card ≤ B := by
  obtain ⟨B,hB⟩ := uniform_local_packing (X:=X) (2*K)
  refine ⟨B,?_⟩
  intro epsilon d he hd x hx J family a t ha ht hnear hsep
  apply hB epsilon he (‖x‖⁻¹ • x) family a _ hsep
  intro j hj
  have hh := direction_of_near_ray x (a j) (t j) (K*epsilon*d) d (ha j hj) (ht j hj) hd hx (hnear j hj)
  rw [dist_comm] at hh
  convert hh using 1
  field_simp
/-- Unoriented version: both signs of a direction are identified, as in the
source. Pairwise projective chordal separation controls overlaps near lines,
not just positively oriented rays. -/
theorem uniform_separated_line_overlap (K : ℝ) (hK : 0 ≤ K) :
    ∃ B : ℕ, ∀ (epsilon d : ℝ), 0 < epsilon → 0 < d → ∀ (x : X), d ≤ ‖x‖ →
    ∀ {J : Type*} (family : Finset J) (a : J → X) (t : J → ℝ),
    (∀ j ∈ family, ‖a j‖ = 1) →
    (∀ j ∈ family, dist x ((t j) • a j) ≤ K*epsilon*d) →
    (∀ j ∈ family, ∀ k ∈ family, j ≠ k →
      epsilon ≤ dist (a j) (a k) ∧ epsilon ≤ dist (a j) (-a k)) → family.card ≤ B := by
  obtain ⟨B,hB⟩ := uniform_separated_ray_overlap (X:=X) K hK
  refine ⟨B,?_⟩
  intro epsilon d he hd x hx J family a t ha hnear hsep
  let oriented := fun j => if 0 ≤ t j then a j else -a j
  have hnorm (j) (hj : j ∈ family) : ‖oriented j‖ = 1 := by
    dsimp [oriented]
    split_ifs <;> simpa using ha j hj
  have hscalar (j) : |t j| • oriented j = t j • a j := by
    dsimp [oriented]
    split_ifs with ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht)]
      simp
  have hneg (z z' : X) : dist (-z) z' = dist z (-z') := by
    rw [dist_eq_norm, dist_eq_norm]
    have heq : -z-z' = -(z-(-z')) := by abel
    rw [heq,norm_neg]
  apply hB epsilon d he hd x hx family oriented (fun j => |t j|) hnorm
    (fun j _ => abs_nonneg _) (fun j hj => by rw [hscalar]; exact hnear j hj)
  intro j hj k hk hne
  have hh := hsep j hj k hk hne
  dsimp [oriented]
  split_ifs
  · exact hh.1
  · exact hh.2
  · rw [hneg]; exact hh.2
  · simpa using hh.1

/-- The shortened-piece overlap estimate needed for summing plane volumes.
A fixed normal map and projectively separated plane directions suffice;
no multiplicity bound is assumed. The constant is uniform in epsilon and d. -/
theorem uniform_shortened_piece_overlap (K : ℝ) (hK : 0 ≤ K) :
    ∃ B : ℕ, ∀ {Z J : Type*} (normal : Z → X) (family : Finset J)
      (directions : J → X) (pieces : J → Set Z) (epsilon d : ℝ),
      0 < epsilon → 0 < d →
      (∀ j ∈ family, ‖directions j‖ = 1) →
      (∀ j ∈ family, ∀ k ∈ family, j ≠ k →
        epsilon ≤ dist (directions j) (directions k) ∧
        epsilon ≤ dist (directions j) (-directions k)) →
      (∀ j ∈ family, ∀ z ∈ pieces j, d ≤ ‖normal z‖ ∧
        ∃ t : ℝ, dist (normal z) (t • directions j) ≤ K*epsilon*d) →
      ∀ z, weightedOverlap family pieces (fun _ => (1:ℝ)) z ≤ B := by
  obtain ⟨B,hB⟩ := uniform_separated_line_overlap (X:=X) K hK
  refine ⟨B,?_⟩
  intro Z J normal family directions pieces epsilon d he hd hn hsep hpieces z
  let selected := family.filter (fun j => z ∈ pieces j)
  have hcount : weightedOverlap family pieces (fun _ => (1:ℝ)) z = (selected.card : ℝ) := by
    simp [weightedOverlap, selected, Set.indicator]
  rw [hcount]
  by_cases hne : selected.Nonempty
  · obtain ⟨j₀,hj₀⟩ := hne
    obtain ⟨hj₀,hz₀⟩ := Finset.mem_filter.mp hj₀
    have hx := (hpieces j₀ hj₀ z hz₀).1
    have hex : ∀ j ∈ selected, ∃ t : ℝ, dist (normal z) (t • directions j) ≤ K*epsilon*d := by
      intro j hj
      obtain ⟨hj,hz⟩ := Finset.mem_filter.mp hj
      exact (hpieces j hj z hz).2
    let t := fun j => if hj : j ∈ selected then Classical.choose (hex j hj) else 0
    have ht : ∀ j ∈ selected, dist (normal z) (t j • directions j) ≤ K*epsilon*d := by
      intro j hj
      dsimp [t]
      rw [dite_eq_left hj]
      exact Classical.choose_spec (hex j hj)
    exact_mod_cast hB epsilon d he hd (normal z) hx selected directions t
      (fun j hj => hn j (Finset.mem_filter.mp hj).1) ht
      (fun j hj k hk hne => hsep j (Finset.mem_filter.mp hj).1 k (Finset.mem_filter.mp hk).1 hne)
  · have hh : selected = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hh]

/- Closeness to a translated plane H+R a gives the required normal-line
approximation. The projection identities and contraction bound are explicit. -/
omit [ProperSpace X] in
theorem normal_line_of_near_plane (P : X →L[ℝ] X) (hP : ‖P‖ ≤ 1)
    (p h a x : X) (t R : ℝ) (hh : P h = 0) (ha : P a = a)
    (hnear : dist x (p+h+t • a) ≤ R) :
    dist (P (x-p)) (t • a) ≤ R := by
  have he : P (x-p) - t • a = P (x-(p+h+t • a)) := by
    rw [map_sub, map_sub, map_add, map_add, map_smul, hh, ha, add_zero]
    abel
  rw [dist_eq_norm, he]
  have hb := P.le_opNorm (x-(p+h+t • a))
  have hc := mul_le_mul_of_nonneg_right hP (norm_nonneg (x-(p+h+t • a)))
  have hn : ‖x-(p+h+t • a)‖ ≤ R := by simpa [dist_eq_norm] using hnear
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.direction_of_near_ray
#print axioms KakeyaTwoScale.uniform_separated_ray_overlap

#print axioms KakeyaTwoScale.uniform_separated_line_overlap

#print axioms KakeyaTwoScale.uniform_shortened_piece_overlap

#print axioms KakeyaTwoScale.normal_line_of_near_plane
