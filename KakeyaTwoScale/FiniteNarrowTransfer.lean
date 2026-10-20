module
public import KakeyaTwoScale.FinalParentPortions
public import KakeyaTwoScale.GridMassSelection
public import KakeyaTwoScale.RetainedParentBrush
public import KakeyaTwoScale.RoundedCoarseArithmetic
public import KakeyaTwoScale.UniformTransfer
public import KakeyaTwoScale.FiniteNarrowMass
public import KakeyaTwoScale.FiniteNarrowInheritance

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Actual finite-scale narrow geometry supplies all three source estimates.
The only narrow input is a measurable initial selection with its already
proved mass and cellwise concentration property. No final retained mass,
parent cap, common point, capture or represented-weight estimate is supplied. -/
theorem finite_lattice_narrow_estimates (n k : ℕ) (R C : ℝ) (shift : ℕ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 4*(n+2:ℝ)+1 ≤ (2:ℝ)^shift) :
    ∃ cA cR cG : ℝ, 0 < cA ∧ 0 < cR ∧ 0 < cG ∧
    ∀ q : ℕ, shift+1 ≤ q → ∀ (d : ℝ) (hd : 0 < d) (_hdr : d ≤ dyadicRadius q),
    ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)),
    Set.InjOn Prod.snd (↑G : Set ((Fin n → ℤ) × (Fin n → ℤ))) →
    ∀ (z w : Fin n → ℝ) (level : ℕ) (i : Fin (n+1)),
    let r := dyadicRadius q
    let b := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.1+z
    let v := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.2+w
    let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) (Real.exp_pos _)
    let U := d^n*(F.children.card:ℝ)
    (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖v j‖ ≤ R) → F.children.Nonempty →
    ∀ (I : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ) (Vf Vc : ℝ), 0 < Vf → 0 < Vc →
    (∀ j, MeasurableSet (I j) ∧ I j ⊆ Set.Icc (0:ℝ) 1) →
    3*U/8 ≤ F.portionMass volume I →
    (∀ t x, (∃ j ∈ F.children, t ∈ I j ∧ gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x) →
      ∃ H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))), Module.finrank ℝ H=k+1 ∧
        ∀ j ∈ F.children, t ∈ I j → gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x →
          planeAngle H (graphUnitDirection i (v j)) ≤ C*r) →
    volume.real (occupiedGridRegion F.children b v d I) ≤ Vf →
    volume.real (occupiedGridRegion F.children b v r (fun _ => Set.Icc (0:ℝ) 1)) ≤ Vc →
    volume.real (occupiedGridRegion F.parents (RoundedParentLevel.parentBase r)
      (RoundedParentLevel.parentSlope r) r (fun _ => Set.Icc (0:ℝ) 1)) ≤ Vc →
    volume.real (⋃ j ∈ F.parents, euclideanTube
      (euclideanUnsplit i (0,RoundedParentLevel.parentBase r j))
      (euclideanUnsplit i (1,RoundedParentLevel.parentSlope r j)) ((2:ℝ)^shift*r)) ≤ Vc →
    ∃ S M : ℝ, 0 ≤ S ∧ 0 ≤ M ∧
      cA*(r^n)^theta*U^a ≤ Vc*F.weight^theta ∧
      (cR*(d/r)^((n:ℝ)*theta))*F.weight^a*U ≤ S*Vf ∧
      (cG*r^n*(r^(k+1))^theta)*S*M ≤ Vc*(q:ℝ) ∧ M*Vc=(1/100:ℝ)*U := by
  obtain ⟨cA,hcA,harith⟩ := rounded_coarse_arithmetic_weight n R hR
  obtain ⟨Cp,hCp,hprune⟩ := rounded_parent_final_portions n
  obtain ⟨cG,hcG,hbrush⟩ := retained_parent_brush n k R (1/100) C shift hR (by norm_num) hC hD
  refine ⟨cA,1/(4*Cp),cG,hcA,by positivity,hcG,?_⟩
  intro q hq d hd hdr G hinj z w level i
  dsimp only
  let r := dyadicRadius q
  let b := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.1+z
  let v := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.2+w
  let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) (Real.exp_pos _)
  let U := d^n*(F.children.card:ℝ)
  intro hb hv hne I Vf Vc hVf hVc hI hstart hnarrow hfine hcoarse hparentVol hcapsuleVol
  have hr : 0 < r := Real.exp_pos _
  have hrone : r ≤ 1 := (dyadicRadius_le_half (by omega)).trans (by norm_num)
  have hU : 0 < U := by dsimp [U]; exact mul_pos (pow_pos hd n) (Nat.cast_pos.mpr (Finset.card_pos.mpr hne))
  have hsep : ∀ j ∈ G, ∀ l ∈ G, j ≠ l → d ≤ dist (v j) (v l) := by
    intro j hj l hl hne
    have hs := latticePoint_separated hd (fun he => hne (hinj hj hl he))
    simpa only [v,dist_add_right] using hs
  obtain ⟨J,hJ,hcap,hK,hKmass,hKcap⟩ := hprune d r hd hr G hinj z w level I Vc hVc hI hstart hcoarse
  let M := ((1/100:ℝ)*U)/Vc
  let K := F.longPortions volume (fun j => safeRetainedHeights F.parents
    (RoundedParentLevel.parentBase r) (RoundedParentLevel.parentSlope r)
    (b j) (v j) F.weight r M (J j)) (1/100)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hKU (j) : K j ⊆ Set.Icc (0:ℝ) 1 := (hK j).2.trans (hI j).2
  have hmasspos : 0 < d^n*∑ j ∈ F.children, volume.real (K j) :=
    (show 0 < U/4 by positivity).trans_le hKmass
  obtain ⟨p,hp,havg⟩ := grid_mass_point F.children b v hd K (fun j _ => (hK j).1)
    (fun j _ => hKU j) hmasspos
  let A := F.children.filter (fun j => p.1 ∈ K j ∧
    gridIndex d (segmentPoint (b j) (v j) p.1)=gridIndex d p.2)
  have havg' : F.portionMass volume K ≤ volume.real (occupiedGridRegion F.children b v d K)*(A.card:ℝ) := by
    have he : A=F.children.filter (fun j => p.1 ∈ K j ∧
        gridIndex d p.2=gridIndex d (segmentPoint (b j) (v j) p.1)) := by
      ext j
      simp only [A,Finset.mem_filter,eq_comm]
    change d^n*∑ j ∈ F.children, volume.real (K j) ≤ _
    rw [he]
    exact havg
  have hregion : occupiedGridRegion F.children b v d K ⊆ occupiedGridRegion F.children b v d I := by
    intro x hx
    obtain ⟨j,hj,ht,hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨j,hj,(hK j).2 ht,hx⟩
  have hvfine := (measureReal_mono hregion (occupiedGridRegion_finite_volume F.children b v hd I
    (fun j _ => (hI j).1) (fun j _ => (hI j).2))).trans hfine
  have hcount : U/4 ≤ Vf*(A.card:ℝ) :=
    hKmass.trans (havg'.trans (mul_le_mul_of_nonneg_right hvfine (by positivity)))
  have hactive : ∃ j ∈ F.children, p.1 ∈ I j ∧
      gridIndex d (segmentPoint (b j) (v j) p.1)=gridIndex d p.2 := by
    obtain ⟨j,hj,ht,hcell⟩ := Set.mem_iUnion₂.mp hp
    exact ⟨j,hj,(hK j).2 ht,hcell.symm⟩
  obtain ⟨H,hdim,hplane⟩ := hnarrow p.1 p.2 hactive
  let bound := Cp*(r/d)^((n:ℝ)*theta)*F.weight^theta
  have hu : 0 < F.weight := F.weight_pos
  have hbound : 0 < bound := by dsimp [bound]; positivity
  have hcellcap (p') (hp' : p' ∈ F.parents) :
      ((F.children.filter (fun j => p.1 ∈ J j ∧
        gridIndex d (segmentPoint (b j) (v j) p.1)=gridIndex d p.2 ∧ F.assign j=p')).card:ℝ) ≤ bound := by
    have he : F.children.filter (fun j => p.1 ∈ J j ∧
        gridIndex d (segmentPoint (b j) (v j) p.1)=gridIndex d p.2 ∧ F.assign j=p') =
        F.children.filter (fun j => F.assign j=p' ∧ p.1 ∈ J j ∧
        gridIndex d (segmentPoint (b j) (v j) p.1)=gridIndex d p.2) := by
      ext j
      simp only [Finset.mem_filter,and_assoc,and_left_comm,and_comm]
    rw [he]
    exact hcap p' hp' p.1 (gridIndex d p.2)
  have hbr := hbrush q hq G b v level d hd hdr hb hv hsep J M bound hM hbound
    (fun j _ => (hJ j).1) (fun j _ => (hJ j).2.trans (hI j).2)
    p.1 p.2 i H hdim hcellcap (fun j hj ht he => hplane j hj ((hJ j).2 ht) he)
  let S := F.weight*(A.card:ℝ)/bound
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hbrush' : (cG*r^n*(r^(k+1))^theta)*S*M ≤ Vc*(q:ℝ) := by
    have hlast := mul_le_mul_of_nonneg_left hcapsuleVol (Nat.cast_nonneg q : (0:ℝ) ≤ q)
    have hh := hbr.trans hlast
    convert hh using 1 <;> ring
  have har := harith G b v level d r hd hdr hrone hv hsep
  have hweight := har.trans (mul_le_mul_of_nonneg_right hparentVol (Real.rpow_nonneg hu.le theta))
  have hrecip : (r/d)^((n:ℝ)*theta)*(d/r)^((n:ℝ)*theta)=1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have he : (r/d)*(d/r)=1 := by field_simp
    rw [he,Real.one_rpow]
  have hupow : F.weight^theta*F.weight^a=F.weight := by
    rw [← Real.rpow_add hu]
    norm_num [theta,a]
  let T := (1/Cp)*(d/r)^((n:ℝ)*theta)*F.weight^a
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hid : bound*T=F.weight := by
    dsimp [bound,T]
    calc
      _ = (Cp*(1/Cp))*((r/d)^((n:ℝ)*theta)*(d/r)^((n:ℝ)*theta))*(F.weight^theta*F.weight^a) := by ring
      _ = _ := by rw [hrecip,hupow]; field_simp
  have hSidentity : S=T*(A.card:ℝ) := by
    dsimp [S]
    apply (div_eq_iff hbound.ne').mpr
    rw [← hid]
    ring
  have hrepresented : ((1/(4*Cp))*(d/r)^((n:ℝ)*theta))*F.weight^a*U ≤ S*Vf := by
    have hh := mul_le_mul_of_nonneg_left hcount hT
    rw [hSidentity]
    convert hh using 1 <;> dsimp [T] <;> ring
  refine ⟨S,M,hS,hM,hweight,hrepresented,hbrush',?_⟩
  change M*Vc=(1/100:ℝ)*U
  dsimp [M]
  field_simp

theorem finite_lattice_narrow_transfer (n k : ℕ) (R C : ℝ) (shift : ℕ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 4*(n+2:ℝ)+1 ≤ (2:ℝ)^shift) :
    ∃ c : ℝ, 0 < c ∧
    ∀ q : ℕ, shift+1 ≤ q → ∀ (d : ℝ) (hd : 0 < d) (_hdr : d ≤ dyadicRadius q),
    ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)),
    Set.InjOn Prod.snd (↑G : Set ((Fin n → ℤ) × (Fin n → ℤ))) →
    ∀ (z w : Fin n → ℝ) (level : ℕ) (i : Fin (n+1)),
    let r := dyadicRadius q
    let b := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.1+z
    let v := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.2+w
    let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) (Real.exp_pos _)
    let U := d^n*(F.children.card:ℝ)
    (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖v j‖ ≤ R) → F.children.Nonempty →
    ∀ (I : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ) (Vf Vc : ℝ), 0 < Vf → 0 < Vc →
    (∀ j, MeasurableSet (I j) ∧ I j ⊆ Set.Icc (0:ℝ) 1) →
    3*U/8 ≤ F.portionMass volume I →
    (∀ t x, (∃ j ∈ F.children, t ∈ I j ∧ gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x) →
      ∃ H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))), Module.finrank ℝ H=k+1 ∧
        ∀ j ∈ F.children, t ∈ I j → gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x →
          planeAngle H (graphUnitDirection i (v j)) ≤ C*r) →
    volume.real (occupiedGridRegion F.children b v d I) ≤ Vf →
    volume.real (occupiedGridRegion F.children b v r (fun _ => Set.Icc (0:ℝ) 1)) ≤ Vc →
    volume.real (occupiedGridRegion F.parents (RoundedParentLevel.parentBase r)
      (RoundedParentLevel.parentSlope r) r (fun _ => Set.Icc (0:ℝ) 1)) ≤ Vc →
    volume.real (⋃ j ∈ F.parents, euclideanTube
      (euclideanUnsplit i (0,RoundedParentLevel.parentBase r j))
      (euclideanUnsplit i (1,RoundedParentLevel.parentSlope r j)) ((2:ℝ)^shift*r)) ≤ Vc →
    c*r^n*(r^(k+1))^theta*(d/r)^((n:ℝ)*theta)*(r^n)^a*U^retainedPower ≤
      Vf*Vc^(2+a/theta)*(q:ℝ) := by
  obtain ⟨cA,cR,cG,hcA,hcR,hcG,hh⟩ := finite_lattice_narrow_estimates n k R C shift hR hC hD
  refine ⟨cG*cR*(1/100)*cA^(a/theta),by positivity,?_⟩
  intro q hq d hd hdr G hinj z w level i
  dsimp only
  let r := dyadicRadius q
  let b := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.1+z
  let v := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.2+w
  let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) (Real.exp_pos _)
  let U := d^n*(F.children.card:ℝ)
  intro hb hv hne I Vf Vc hVf hVc hI hstart hnarrow hfine hcoarse hparentVol hcapsuleVol
  have hr : 0 < r := Real.exp_pos _
  have hU : 0 < U := mul_pos (pow_pos hd n) (Nat.cast_pos.mpr (Finset.card_pos.mpr hne))
  obtain ⟨S,M,hS,hM,hweight,hrep,hbrush,hthreshold⟩ :=
    hh q hq d hd hdr G hinj z w level i hb hv hne I Vf Vc hVf hVc hI hstart hnarrow
      hfine hcoarse hparentVol hcapsuleVol
  have ht := transfer_of_weight_and_brush Vf Vc F.weight U S M (1/100) (q:ℝ)
    (cA*(r^n)^theta*U^a) (cR*(d/r)^((n:ℝ)*theta)) (cG*r^n*(r^(k+1))^theta)
    hVf.le hVc F.weight_pos hU.le (by norm_num) (by positivity) (by positivity)
    (by positivity) hweight hrep hbrush hthreshold
  have hp : (cA*(r^n)^theta*U^a)^(a/theta) = cA^(a/theta)*(r^n)^a*U^(a*(a/theta)) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hcA.le (by positivity), ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul hU.le]
    congr 2
    congr 1
    norm_num [theta,a]
  have hu : U^(a*(a/theta))*U^2=U^retainedPower := by
    rw [show U^2=U^(2:ℝ) by simp, ← Real.rpow_add hU]
    congr 1
    unfold retainedPower
    ring
  rw [hp] at ht
  have he : (cG*r^n*(r^(k+1))^theta)*(cR*(d/r)^((n:ℝ)*theta))*(1/100)*
      (cA^(a/theta)*(r^n)^a*U^(a*(a/theta)))*U^2 =
      (cG*cR*(1/100)*cA^(a/theta))*r^n*(r^(k+1))^theta*(d/r)^((n:ℝ)*theta)*(r^n)^a*U^retainedPower := by
    rw [← hu]
    ring
  rw [he] at ht
  exact ht

/-- Literal finite narrow transfer from the actual broad mass alternative.
All retained selections and geometric witnesses are constructed internally. -/
theorem finite_lattice_narrow_transfer_of_broad_mass (n k : ℕ) (R C : ℝ) (shift : ℕ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 4*(n+2:ℝ)+1 ≤ (2:ℝ)^shift) :
    ∃ c : ℝ, 0 < c ∧
    ∀ q : ℕ, shift+1 ≤ q → ∀ (d : ℝ) (hd : 0 < d) (_hdr : d ≤ dyadicRadius q),
    ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)),
    Set.InjOn Prod.snd (↑G : Set ((Fin n → ℤ) × (Fin n → ℤ))) →
    ∀ (z w : Fin n → ℝ) (level : ℕ) (i : Fin (n+1)),
    let r := dyadicRadius q
    let b := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.1+z
    let v := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.2+w
    let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) (Real.exp_pos _)
    let U := d^n*(F.children.card:ℝ)
    (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖v j‖ ≤ R) → F.children.Nonempty →
    ∀ (Vf Vc : ℝ), 0 < Vf → 0 < Vc →
    (∫ x in finiteGridBroadRegion F.children b v (fun j => graphUnitDirection i (v j))
      (k+1) d (C*r), gridMultiplicity F.children b v d x) ≤ U/4 →
    volume.real (occupiedGridRegion F.children b v d (fun _ => Set.Icc (0:ℝ) 1)) ≤ Vf →
    volume.real (occupiedGridRegion F.children b v r (fun _ => Set.Icc (0:ℝ) 1)) ≤ Vc →
    volume.real (occupiedGridRegion F.parents (RoundedParentLevel.parentBase r)
      (RoundedParentLevel.parentSlope r) r (fun _ => Set.Icc (0:ℝ) 1)) ≤ Vc →
    volume.real (⋃ j ∈ F.parents, euclideanTube
      (euclideanUnsplit i (0,RoundedParentLevel.parentBase r j))
      (euclideanUnsplit i (1,RoundedParentLevel.parentSlope r j)) ((2:ℝ)^shift*r)) ≤ Vc →
    c*r^n*(r^(k+1))^theta*(d/r)^((n:ℝ)*theta)*(r^n)^a*U^retainedPower ≤
      Vf*Vc^(2+a/theta)*(q:ℝ) := by
  obtain ⟨c,hc,hh⟩ := finite_lattice_narrow_transfer n k R C shift hR hC hD
  refine ⟨c,hc,?_⟩
  intro q hq d hd hdr G hinj z w level i
  dsimp only
  let r := dyadicRadius q
  let b := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.1+z
  let v := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.2+w
  let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) (Real.exp_pos _)
  intro hb hv hne Vf Vc hVf hVc hbroad hfine hcoarse hparents hcapsules
  let u := fun j => graphUnitDirection i (v j)
  let I := finiteNarrowGridHeights F.children b v u (k+1) d (C*r)
  have hI : ∀ j, MeasurableSet (I j) ∧ I j ⊆ Set.Icc (0:ℝ) 1 := by
    intro j
    exact ⟨measurableSet_finiteNarrowGridHeights F.children b v u (k+1) d (C*r) j,
      fun _ hx => hx.1⟩
  have hmass := finite_narrow_grid_retained_mass F.children b v u (k+1) d (C*r) hd hbroad
  have hnarrow : ∀ t x,
      (∃ j ∈ F.children, t ∈ I j ∧ gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x) →
      ∃ H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))), Module.finrank ℝ H=k+1 ∧
        ∀ j ∈ F.children, t ∈ I j → gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x →
          planeAngle H (graphUnitDirection i (v j)) ≤ C*r := by
    intro t x hx
    obtain ⟨j,hj,ht,he⟩ := hx
    obtain ⟨H,hH,hp⟩ := finiteNarrowGrid_inherited_plane F.children b v u (k+1) d (C*r)
      I (fun _ _ => Set.Subset.refl _) t x ⟨j,hj,ht,he.symm⟩
    exact ⟨H,hH,fun l hl hlt hle => hp l hl hlt hle.symm⟩
  have hsub : occupiedGridRegion F.children b v d I ⊆
      occupiedGridRegion F.children b v d (fun _ => Set.Icc (0:ℝ) 1) := by
    intro x hx
    obtain ⟨j,hj,ht,hcell⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨j,hj,(hI j).2 ht,hcell⟩
  have hvol := (measureReal_mono hsub (occupiedGridRegion_finite_volume F.children b v hd
    (fun _ => Set.Icc (0:ℝ) 1) (fun _ _ => measurableSet_Icc) (fun _ _ => Set.Subset.refl _))).trans hfine
  exact hh q hq d hd hdr G hinj z w level i hb hv hne I Vf Vc hVf hVc hI hmass hnarrow
    hvol hcoarse hparents hcapsules

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_lattice_narrow_estimates

#print axioms KakeyaTwoScale.finite_lattice_narrow_transfer

#print axioms KakeyaTwoScale.finite_lattice_narrow_transfer_of_broad_mass
