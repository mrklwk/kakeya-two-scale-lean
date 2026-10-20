module
public import KakeyaTwoScale.RetainedTupleMarginalMass
public import KakeyaTwoScale.ShortComponentTerminal

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- The retained fiber injects into the product of its OWN marginal images.
This does not assert that the retained relation is a Cartesian product. -/
theorem retained_capacity_le_marginal_product {T Q O : Type*}
    [DecidableEq T] [DecidableEq Q] [DecidableEq O] {k : ℕ}
    (hk : 0 < k) (Y : Finset T) (cube : T → Q) (original : T → Fin k → O)
    (hinj : ∀ y∈Y, ∀ z∈Y, cube y=cube z → original y=original z → y=z) (q : Q) :
    ParentLevel.capacity Y cube q ≤ ∏ j, (retainedCubeMarginal Y cube original j q).card := by
  classical
  let j : Fin k := ⟨0,hk⟩
  have h := retained_capacity_le_one_marginal Y cube original
    (fun l q => retainedCubeMarginal Y cube original l q)
    (by
      intro y hy l
      exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,rfl⟩,rfl⟩)
    hinj j q
  rwa [Finset.mul_prod_erase Finset.univ
    (fun l => (retainedCubeMarginal Y cube original l q).card) (Finset.mem_univ j)] at h

/-- A bounded fiber cap converts a larger nonlinear exponent to a smaller
one. The exponent difference is exact; zero fibers are included. -/
theorem tuple_mass_le_cap_mul_smaller_mass {T Q : Type*}
    [DecidableEq Q] (Y : Finset T) (cube : T→Q) (cubes : Finset Q)
    {p r M : ℝ} (hr : 0<r) (hp : r≤p)
    (hcap : ∀ q∈cubes, (ParentLevel.capacity Y cube q:ℝ)≤M) :
    tupleCubeMass Y cube cubes p ≤ M^(p-r)*tupleCubeMass Y cube cubes r := by
  unfold tupleCubeMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hz : 0≤(ParentLevel.capacity Y cube q:ℝ) := Nat.cast_nonneg _
  have hp0 : 0<p := hr.trans_le hp
  have he : (ParentLevel.capacity Y cube q:ℝ)^p =
      (ParentLevel.capacity Y cube q:ℝ)^(p-r)*(ParentLevel.capacity Y cube q:ℝ)^r := by
    rw [← Real.rpow_add' hz (by linarith : p-r+r≠0)]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hz (hcap q hq) (sub_nonneg.mpr hp)) (Real.rpow_nonneg hz r)

/-- Finite Hölder on actual marginal images. No lower bound for any retained
marginal relative to its root marginal is assumed. -/
theorem retained_tuple_mass_reciprocal_le_geometric_incidence {T Q O : Type*}
    [DecidableEq T] [DecidableEq Q] [DecidableEq O] {k : ℕ}
    (hk : 0<k) (Y : Finset T) (hY : Y.Nonempty) (cube : T→Q) (cubes : Finset Q)
    (hsupport : ∀ y∈Y, cube y∈cubes) (original : T→Fin k→O)
    (hinj : ∀ y∈Y, ∀ z∈Y, cube y=cube z → original y=original z → y=z) :
    tupleCubeMass Y cube cubes (1/(k:ℝ)) ≤
      (∏ j, ∑ q∈cubes, ((retainedCubeMarginal Y cube original j q).card:ℝ))^(1/(k:ℝ)) := by
  classical
  let a : Fin k→Q→ℝ := fun j q => (retainedCubeMarginal Y cube original j q).card
  let I : Fin k→ℝ := fun j => ∑ q∈cubes, a j q
  have ha (j q) : 0≤a j q := Nat.cast_nonneg _
  have hI (j) : 0<I j := by
    obtain ⟨y,hy⟩ := hY
    have hne : (retainedCubeMarginal Y cube original j (cube y)).Nonempty :=
      ⟨original y j,Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,rfl⟩,rfl⟩⟩
    have hp : 0<a j (cube y) := by
      dsimp [a]
      exact_mod_cast Finset.card_pos.mpr hne
    exact hp.trans_le (Finset.single_le_sum (fun q _ => ha j q) (hsupport y hy))
  have hpoint (q : Q) : (ParentLevel.capacity Y cube q:ℝ)≤∏ j, a j q := by
    dsimp [a]
    exact_mod_cast retained_capacity_le_marginal_product hk Y cube original hinj q
  have hfirst : tupleCubeMass Y cube cubes (1/(k:ℝ)) ≤ ∑ q∈cubes, (∏ j, a j q)^(1/(k:ℝ)) :=
    Finset.sum_le_sum (fun q _ => Real.rpow_le_rpow (Nat.cast_nonneg _) (hpoint q) (by positivity))
  exact hfirst.trans (sum_product_rpow_le_of_family_sums cubes hk a I
    (fun j q => ha j q) hI (fun _ => le_rfl) le_rfl)

/-- The repaired central estimate. Root-density losses never enter: the only
normalization is an upper cap on the ACTUAL tuple fiber and its actual mass. -/
theorem retained_tuple_mass_le_cap_geometric_incidence {T Q O : Type*}
    [DecidableEq T] [DecidableEq Q] [DecidableEq O] {k : ℕ}
    (hk : 0<k) (Y : Finset T) (hY : Y.Nonempty) (cube : T→Q) (cubes : Finset Q)
    (hsupport : ∀ y∈Y, cube y∈cubes) (original : T→Fin k→O)
    (hinj : ∀ y∈Y, ∀ z∈Y, cube y=cube z → original y=original z → y=z)
    {p M : ℝ} (hp : 1/(k:ℝ)≤p) (hM : 0≤M)
    (hcap : ∀ q∈cubes, (ParentLevel.capacity Y cube q:ℝ)≤M) :
    tupleCubeMass Y cube cubes p ≤ M^(p-1/(k:ℝ))*
      (∏ j, ∑ q∈cubes, ((retainedCubeMarginal Y cube original j q).card:ℝ))^(1/(k:ℝ)) := by
  have hkR : 0<(k:ℝ) := by exact_mod_cast hk
  exact (tuple_mass_le_cap_mul_smaller_mass Y cube cubes (by positivity) hp hcap).trans
    (mul_le_mul_of_nonneg_left
      (retained_tuple_mass_reciprocal_le_geometric_incidence hk Y hY cube cubes hsupport original hinj)
      (Real.rpow_nonneg hM _))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.retained_capacity_le_marginal_product
#print axioms KakeyaTwoScale.tuple_mass_le_cap_mul_smaller_mass
#print axioms KakeyaTwoScale.retained_tuple_mass_reciprocal_le_geometric_incidence
#print axioms KakeyaTwoScale.retained_tuple_mass_le_cap_geometric_incidence
