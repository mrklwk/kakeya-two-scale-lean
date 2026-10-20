module
public import KakeyaTwoScale.FiberPartitionEncoding

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- A fixed finite rational slope family embeds into one fixed consecutive
integer interval after one positive dilation and translation. -/
theorem exists_consecutive_slope_indices (R : Finset ℚ) :
    ∃ q B ell : ℕ, 0 < q ∧ 2 ≤ ell ∧ ∃ j : ℚ → ℕ,
      ∀ r ∈ R, j r < ell ∧ (j r:ℚ) = (B:ℚ)+(q:ℚ)*r := by
  obtain ⟨q,hq,hd⟩ := finite_clear_denominators R
  have hz (r : ℚ) : ∃ z : ℤ, r ∈ R → (z:ℚ) = (q:ℚ)*r := by
    by_cases hr : r ∈ R
    · obtain ⟨z,hz⟩ := hd r hr
      exact ⟨z,fun _ => hz⟩
    · exact ⟨0,fun h => (hr h).elim⟩
  choose z hz using hz
  let B := R.sup (fun r => (z r).natAbs)
  let j := fun r => ((B:ℤ)+z r).toNat
  refine ⟨q,B,2*B+2,hq,by omega,j,?_⟩
  intro r hr
  have hB : (z r).natAbs ≤ B := Finset.le_sup (f := fun r => (z r).natAbs) hr
  have habs : |z r| ≤ (B:ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hB
  have hlow : 0 ≤ (B:ℤ)+z r := by have := (abs_le.mp habs).1; linarith
  have hhi : (B:ℤ)+z r ≤ 2*(B:ℤ) := by have := (abs_le.mp habs).2; linarith
  have he : (j r:ℤ) = (B:ℤ)+z r := Int.toNat_of_nonneg hlow
  refine ⟨?_,?_⟩
  · have hh : j r ≤ 2*B := by exact_mod_cast (show (j r:ℤ) ≤ 2*(B:ℤ) by rw [he]; exact hhi)
    omega
  · have hh : (j r:ℚ) = (B:ℚ)+(z r:ℚ) := by exact_mod_cast he
    rwa [hz r hr] at hh

def slopeAffinePair {n : ℕ} (B q : ℚ) (v : (Fin n → ℚ) × (Fin n → ℚ)) :
    (Fin n → ℚ) × (Fin n → ℚ) := (v.1+B • v.2,q • v.2)

theorem slopeAffinePair_height_iff {n : ℕ} (B q : ℚ) (hq : q ≠ 0)
    (v w : (Fin n → ℚ) × (Fin n → ℚ)) :
    (slopeAffinePair B q v).2 = (slopeAffinePair B q w).2 ↔ v.2=w.2 := by
  constructor
  · intro h
    funext i
    have hh := congrFun h i
    exact mul_left_cancel₀ hq hh
  · intro h
    simp only [slopeAffinePair,h]

theorem slopeAffinePair_injective {n : ℕ} (B q : ℚ) (hq : q ≠ 0) :
    Function.Injective (slopeAffinePair (n:=n) B q) := by
  intro v w h
  have hv := (slopeAffinePair_height_iff B q hq v w).mp (congrArg Prod.snd h)
  have hb := congrArg Prod.fst h
  dsimp [slopeAffinePair] at hb
  rw [hv] at hb
  exact Prod.ext (add_right_cancel hb) hv

theorem slopeAffinePair_projection {n : ℕ} (B q r s : ℚ) (hs : s=B+q*r)
    (v : (Fin n → ℚ) × (Fin n → ℚ)) :
    vectorProjection r (slopeAffinePair B q v) = vectorProjection s v := by
  funext i
  simp only [vectorProjection,slopeAffinePair,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hs]
  ring

/-- The full consecutive-slope arithmetic inequality in every finite rational
vector dimension, with a single ell fixed independently of dimension and G.
The empty graph is included. -/
theorem consecutive_vector_partition_625_373 :
    ∃ ell : ℕ, 2 ≤ ell ∧ ∀ n : ℕ,
      ∀ G : Finset ((Fin n → ℚ) × (Fin n → ℚ)),
      ∃ i : ℕ, i < ell ∧ fiberCardPartition G Prod.snd (252/373) ≤
        ((G.image (vectorProjection (i:ℚ))).card:ℝ)^(625/373:ℝ) := by
  obtain ⟨R,_hR,hcount⟩ := finite_homogeneous_vector_partition_625_373
  obtain ⟨q,B,ell,hq,hell,j,hj⟩ := exists_consecutive_slope_indices R
  refine ⟨ell,hell,?_⟩
  intro n G
  by_cases hG : G.Nonempty
  · have hqQ : (q:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
    let e := slopeAffinePair (n:=n) (B:ℚ) (q:ℚ)
    have he := slopeAffinePair_injective (n:=n) (B:ℚ) (q:ℚ) hqQ
    have hv := fun v (_ : v ∈ G) w (_ : w ∈ G) => slopeAffinePair_height_iff (B:ℚ) (q:ℚ) hqQ v w
    obtain ⟨r,hr,hh⟩ := hcount n (G.image e) (hG.image e)
    have hpart := fiberCardPartition_encoding G e Prod.snd Prod.snd he.injOn hv (252/373)
    have himage : (G.image e).image (vectorProjection r) = G.image (vectorProjection (j r:ℚ)) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro v _
      exact slopeAffinePair_projection (B:ℚ) (q:ℚ) r (j r:ℚ) (hj r hr).2 v
    rw [hpart,himage] at hh
    exact ⟨j r,(hj r hr).1,hh⟩
  · have he : G=∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    refine ⟨0,by omega,?_⟩
    rw [he]
    simp only [fiberCardPartition,Finset.image_empty,Finset.sum_empty,Finset.card_empty,Nat.cast_zero]
    exact Real.rpow_nonneg (by norm_num) _

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_consecutive_slope_indices
#print axioms KakeyaTwoScale.slopeAffinePair_height_iff
#print axioms KakeyaTwoScale.slopeAffinePair_injective
#print axioms KakeyaTwoScale.slopeAffinePair_projection
#print axioms KakeyaTwoScale.consecutive_vector_partition_625_373
