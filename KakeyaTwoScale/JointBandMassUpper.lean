module
public import KakeyaTwoScale.ConcreteRootBandLoss

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem tupleCubeMass_image {T Q : Type*} [DecidableEq T] [DecidableEq Q]
    (Y : Finset T) (cube : T→Q) (cubes : Finset Q) (p : ℝ) (hp : 0<p)
    (hs : Y.image cube⊆cubes) :
    tupleCubeMass Y cube cubes p=tupleCubeMass Y cube (Y.image cube) p := by
  unfold tupleCubeMass
  symm
  apply Finset.sum_subset hs
  intro q _ hq
  have he : Y.filter (fun y => cube y=q)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hq (Finset.mem_image.mpr ⟨y,(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2⟩)
  simp only [ParentLevel.capacity,he,Finset.card_empty,Nat.cast_zero,Real.zero_rpow hp.ne']

theorem joint_band_mass_upper {T Q : Type*} [DecidableEq T] [DecidableEq Q]
    (Y : Finset T) (cube : T→Q) (cubes : Finset Q) (p M : ℝ) (hp : 0<p)
    (hs : Y.image cube⊆cubes)
    (hband : ∀q∈Y.image cube, (ParentLevel.capacity Y cube q:ℝ)≤M) :
    tupleCubeMass Y cube cubes p≤((Y.image cube).card:ℝ)*M^p := by
  rw [tupleCubeMass_image Y cube cubes p hp hs]
  unfold tupleCubeMass
  calc
    _ ≤ ∑_q∈Y.image cube, M^p := Finset.sum_le_sum (fun q hq =>
      Real.rpow_le_rpow (Nat.cast_nonneg _) (hband q hq) hp.le)
    _ = _ := by simp

theorem joint_band_power {k : ℕ} {B mu : ℝ} (hk : 0<k) (hB : 1<B) (hmu : 0 < mu) :
    ((2:ℝ)*mu^k)^(B/((k:ℝ)*(B-1)))=
      (2:ℝ)^(B/((k:ℝ)*(B-1)))*mu^(B/(B-1)) := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (pow_nonneg hmu.le _),
    ←Real.rpow_natCast,←Real.rpow_mul hmu.le]
  congr 2
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  field_simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.joint_band_mass_upper
#print axioms KakeyaTwoScale.joint_band_power
