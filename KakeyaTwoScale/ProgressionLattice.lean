module
public import KakeyaTwoScale.LatticePacking
public import KakeyaTwoScale.ArithmeticCounting

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- One rounding at the progression's initial height; the same error is
then used at every height. -/
def progressionLatticeMap {n : ℕ} (r s h : ℝ)
    (p : (Fin n → ℤ) × (Fin n → ℤ)) : (Fin n → ℤ) × (Fin n → ℤ) :=
  (gridIndex (h*r/4) (segmentPoint (latticePoint r p.1) (latticePoint r p.2) s),
    (4:ℤ) • p.2)

theorem progressionLatticeMap_slope {n : ℕ} (r s h : ℝ)
    (p q : (Fin n → ℤ) × (Fin n → ℤ)) :
    (progressionLatticeMap r s h p).2=(progressionLatticeMap r s h q).2 ↔ p.2=q.2 := by
  constructor
  · intro he; funext j
    have hh := congrFun he j
    change (4:ℤ)*p.2 j=4*q.2 j at hh
    omega
  · intro he; simp [progressionLatticeMap,he]

theorem progressionLatticeMap_injective {n : ℕ} {r h : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hh1 : h ≤ 1) (s : ℝ) :
    Function.Injective (progressionLatticeMap (n:=n) r s h) := by
  intro p q he
  have hv := (progressionLatticeMap_slope r s h p q).mp (congrArg Prod.snd he)
  have hb := congrArg Prod.fst he
  change gridIndex (h*r/4) (latticePoint r p.1+s • latticePoint r p.2) =
    gridIndex (h*r/4) (latticePoint r q.1+s • latticePoint r q.2) at hb
  rw [hv] at hb
  have hdr : 2*(h*r/4) < r := by nlinarith
  exact Prod.ext (gridIndex_translated_lattice_injective hr (by positivity) hdr _ hb) hv

/-- Exact real reconstruction of every integer projection. -/
theorem progressionLatticeMap_projection {n : ℕ} (r s h : ℝ) (i : ℕ)
    (p : (Fin n → ℤ) × (Fin n → ℤ)) :
    latticePoint (h*r/4) (integerVectorProjection i (progressionLatticeMap r s h p)) =
      gridRound (h*r/4) (segmentPoint (latticePoint r p.1) (latticePoint r p.2) s)+
        ((i:ℝ)*h) • latticePoint r p.2 := by
  funext j
  simp only [latticePoint,integerVectorProjection,progressionLatticeMap,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,Int.cast_add,Int.cast_mul,Int.cast_natCast,
    Int.cast_ofNat,gridRound]
  ring

/-- Arbitrary intercept and slope translations are a common drift. They do
not enter the integer encoding or its error bound. -/
theorem progressionLatticeMap_close {n : ℕ} {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    (s : ℝ) (i : ℕ) (p : (Fin n → ℤ) × (Fin n → ℤ))
    (z w : Fin n → ℝ) :
    dist (latticePoint (h*r/4) (integerVectorProjection i (progressionLatticeMap r s h p))+
      (z+(s+(i:ℝ)*h) • w))
      (segmentPoint (latticePoint r p.1+z) (latticePoint r p.2+w) (s+(i:ℝ)*h)) ≤ h*r/4 := by
  rw [progressionLatticeMap_projection]
  have he : segmentPoint (latticePoint r p.1+z) (latticePoint r p.2+w) (s+(i:ℝ)*h) =
      (segmentPoint (latticePoint r p.1) (latticePoint r p.2) s+
        ((i:ℝ)*h) • latticePoint r p.2)+(z+(s+(i:ℝ)*h) • w) := by
    funext j
    simp only [segmentPoint,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,dist_add_right,dist_add_right,dist_comm]
  exact dist_gridRound_le (by positivity) _

/-- The actual integer encoding preserves every occupied slope fiber. -/
theorem progressionLatticeMap_partition {n : ℕ} {r h : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hh1 : h ≤ 1) (s p : ℝ)
    (G : Finset ((Fin n → ℤ) × (Fin n → ℤ))) :
    fiberCardPartition (G.image (progressionLatticeMap r s h)) Prod.snd p =
      fiberCardPartition G Prod.snd p :=
  fiberCardPartition_encoding G _ _ _ (progressionLatticeMap_injective hr hh hh1 s).injOn
    (fun u _ v _ => progressionLatticeMap_slope r s h u v) p

/-- For a fixed positive step cutoff, projection counting is controlled by
actual occupied cells with a constant preceding all scales, heights, finite
families and lattice translations. -/
theorem rounded_progression_projection_bound (n : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ B : ℕ, 0 < B ∧ ∀ (r s h : ℝ), 0 < r → c ≤ h →
      ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)), ∀ z w : Fin n → ℝ, ∀ i : ℕ,
      ((G.image (progressionLatticeMap r s h)).image (integerVectorProjection i)).card ≤
        B*(G.image (fun p => gridIndex r
          (segmentPoint (latticePoint r p.1+z) (latticePoint r p.2+w) (s+(i:ℝ)*h)))).card := by
  obtain ⟨B,hB,hbound⟩ := lattice_projection_cell_bound n (4/c)
  refine ⟨B,hB,?_⟩
  intro r s h hr hch G z w i
  have hh : 0 < h := hc.trans_le hch
  have hrd : r ≤ (4/c)*(h*r/4) := by
    field_simp
    nlinarith
  rw [Finset.image_image]
  exact hbound r (h*r/4) hr (by positivity) hrd G
    (fun p => segmentPoint (latticePoint r p.1+z) (latticePoint r p.2+w) (s+(i:ℝ)*h))
    (fun p => integerVectorProjection i (progressionLatticeMap r s h p))
    (z+(s+(i:ℝ)*h) • w)
    (fun p _ => progressionLatticeMap_close hr hh s i p z w)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.progressionLatticeMap_slope
#print axioms KakeyaTwoScale.progressionLatticeMap_injective
#print axioms KakeyaTwoScale.progressionLatticeMap_projection
#print axioms KakeyaTwoScale.progressionLatticeMap_close
#print axioms KakeyaTwoScale.progressionLatticeMap_partition
#print axioms KakeyaTwoScale.rounded_progression_projection_bound
