module
public import KakeyaTwoScale.KakeyaSelectedFamily
public import KakeyaTwoScale.FiniteBroadZahl
public import KakeyaTwoScale.FiniteNarrowScale

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale
open Classical

variable {K : Set (EuclideanSpace ℝ (Fin (n+1)))} {R cU : ℝ} {q : ℕ}

def selectedMass (n : ℕ) {K : Set (EuclideanSpace ℝ (Fin (n+1)))}
    {R cU : ℝ} {q : ℕ} (data : KakeyaScaleData n K R q cU) : ℝ :=
  (dyadicRadius (20*q))^n*((dyadicRoundedFamily n data.G data.level q).children.card:ℝ)

def selectedBroadIntegral (n k : ℕ) {K : Set (EuclideanSpace ℝ (Fin (n+1)))}
    {R cU : ℝ} {q : ℕ} (data : KakeyaScaleData n K R q cU) : ℝ :=
  ∫ x in finiteGridBroadRegion (dyadicRoundedFamily n data.G data.level q).children
    (dyadicLatticeBase n q) (dyadicLatticeSlope n q)
    (fun j => graphUnitDirection 0 (dyadicLatticeSlope n q j)) (k-1)
    (dyadicRadius (20*q)) (dyadicRadius q),
    gridMultiplicity (dyadicRoundedFamily n data.G data.level q).children
      (dyadicLatticeBase n q) (dyadicLatticeSlope n q) (dyadicRadius (20*q)) x

def selectedBroad (n k : ℕ) {K : Set (EuclideanSpace ℝ (Fin (n+1)))}
    {R cU : ℝ} {q : ℕ} (data : KakeyaScaleData n K R q cU) : Prop :=
  selectedMass n data/4 ≤ selectedBroadIntegral n k data

theorem selected_children_subset (n : ℕ) {K : Set (EuclideanSpace ℝ (Fin (n+1)))}
    {R cU : ℝ} {q : ℕ} (data : KakeyaScaleData n K R q cU) :
    (dyadicRoundedFamily n data.G data.level q).children ⊆ data.G :=
  ParentLevel.selected_subset _ _ _

theorem dyadic_fine_lt_half {q : ℕ} (hq : 1≤q) : dyadicRadius (20*q)<1/2 := by
  have he : dyadicRadius 1=(1/2:ℝ) := by
    unfold dyadicRadius
    simp only [Nat.cast_one,mul_one,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [← he]
  unfold dyadicRadius
  apply Real.exp_lt_exp.mpr
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hq' : (1:ℝ)<20*q := by exact_mod_cast (by omega : 1<20*q)
  push_cast
  nlinarith

theorem selected_broad_scale_transfer (n k : ℕ) (Z : ZahlCapsuleEstimate (n+1) k) :
    ∀ ε : ℝ, 0<ε → ∃ c : ℝ, 0<c ∧ ∀ q : ℕ, 1≤q →
    ∀ (K : Set (EuclideanSpace ℝ (Fin (n+1)))) (R cU : ℝ)
      (data : KakeyaScaleData n K R q cU) (Vf : ℝ),
    selectedBroad n k data →
    volume.real (occupiedGridRegion (dyadicRoundedFamily n data.G data.level q).children
      (dyadicLatticeBase n q) (dyadicLatticeSlope n q) (dyadicRadius (20*q))
      (fun _ => Set.Icc (0:ℝ) 1)) ≤ Vf →
    c*(dyadicRadius (20*q))^((n+1:ℝ)-zahlB (n+1) k+ε)*
      (dyadicRadius q)^((k:ℝ)-1)*(selectedMass n data)^(((n+1:ℝ)-zahlB (n+1) k)/n) ≤ Vf := by
  intro ε hε
  obtain ⟨c,hc,hh⟩ := finite_lattice_broad_transfer n k Z 1 (by norm_num) ε hε
  refine ⟨c,hc,?_⟩
  intro q hq K R cU data Vf hP hV
  have hsub := selected_children_subset n data
  have hinj := data.slope_injective.mono hsub
  have hb := hh (dyadicRadius (20*q)) (dyadicRadius q) (Real.exp_pos _)
    (dyadic_fine_lt_half hq) (Real.exp_pos _)
    (dyadicRoundedFamily n data.G data.level q).children data.selected_nonempty hinj 0 0 0
  simp only [add_zero] at hb
  exact (hb (fun j hj => data.slope_bound j (hsub hj)) hP).trans hV

theorem selected_narrow_scale_transfer (n k : ℕ) (R : ℝ) (shift : ℕ)
    (hk : 2≤k) (hR : 0≤R) (hD : 4*(n+2:ℝ)+1≤(2:ℝ)^shift) :
    ∃ c : ℝ, 0<c ∧ ∀ q : ℕ, shift+1≤q →
    ∀ (K : Set (EuclideanSpace ℝ (Fin (n+1)))) (cU : ℝ)
      (data : KakeyaScaleData n K R q cU) (Vf Vc : ℝ), 0<Vf → 0<Vc →
    ¬selectedBroad n k data →
    volume.real (occupiedGridRegion (dyadicRoundedFamily n data.G data.level q).children
      (dyadicLatticeBase n q) (dyadicLatticeSlope n q) (dyadicRadius (20*q))
      (fun _ => Set.Icc (0:ℝ) 1)) ≤ Vf →
    volume.real (occupiedGridRegion (dyadicRoundedFamily n data.G data.level q).children
      (dyadicLatticeBase n q) (dyadicLatticeSlope n q) (dyadicRadius q)
      (fun _ => Set.Icc (0:ℝ) 1)) ≤ Vc →
    volume.real (occupiedGridRegion (dyadicRoundedFamily n data.G data.level q).parents
      (RoundedParentLevel.parentBase (dyadicRadius q))
      (RoundedParentLevel.parentSlope (dyadicRadius q)) (dyadicRadius q)
      (fun _ => Set.Icc (0:ℝ) 1)) ≤ Vc →
    volume.real (⋃ j ∈ (dyadicRoundedFamily n data.G data.level q).parents,
      euclideanTube (euclideanUnsplit 0 (0,RoundedParentLevel.parentBase (dyadicRadius q) j))
        (euclideanUnsplit 0 (1,RoundedParentLevel.parentSlope (dyadicRadius q) j))
        ((2:ℝ)^shift*dyadicRadius q)) ≤ Vc →
    c*Real.exp (-Real.log 2*transferExponent (n+1:ℕ) k*q)*(selectedMass n data)^retainedPower ≤
      Vf*Vc^(2+a/theta)*(q:ℝ) := by
  obtain ⟨c,hc,hh⟩ := finite_lattice_narrow_transfer_of_broad_mass n (k-2) (R+1) 1 shift
    (by linarith) (by norm_num) hD
  refine ⟨c,hc,?_⟩
  intro q hq K cU data Vf Vc hVf hVc hP hfine hcoarse hparents hcaps
  have hdr : dyadicRadius (20*q)≤dyadicRadius q := by
    unfold dyadicRadius
    apply Real.exp_le_exp.mpr
    have hlog : 0≤Real.log 2 := (Real.log_pos (by norm_num)).le
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) q]
  have hb := hh q hq (dyadicRadius (20*q)) (Real.exp_pos _) hdr data.G
    data.slope_injective 0 0 data.level 0
  dsimp only at hb
  simp only [add_zero,one_mul,show k-2+1=k-1 by omega] at hb
  have hv : ∀ j∈data.G, ‖dyadicLatticeSlope n q j‖≤R+1 :=
    fun j hj => (data.slope_bound j hj).trans (by linarith)
  have hm : selectedBroadIntegral n k data≤selectedMass n data/4 :=
    (lt_of_not_ge hP).le
  have ht := hb data.base_bound hv data.selected_nonempty Vf Vc hVf hVc hm
    hfine hcoarse hparents hcaps
  have hs := finite_narrow_dyadic_scale n (k-2) q
  rw [show k-2+2=k by omega] at hs
  calc
    _ = c*((dyadicRadius q)^n*((dyadicRadius q)^(k-2+1))^theta*
      (dyadicRadius (20*q)/dyadicRadius q)^((n:ℝ)*theta)*((dyadicRadius q)^n)^a)*
      (selectedMass n data)^retainedPower := by rw [hs]
    _ ≤ _ := by simpa only [selectedMass,dyadicRoundedFamily,dyadicLatticeBase,dyadicLatticeSlope,mul_assoc,show k-2+1=k-1 by omega] using ht

end KakeyaTwoScale
#print axioms KakeyaTwoScale.selected_broad_scale_transfer
#print axioms KakeyaTwoScale.selected_narrow_scale_transfer
