module
public import KakeyaTwoScale.FixedParentPruning
public import KakeyaTwoScale.RoundedParentLevel

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The actual immutable parent capacity gives the source's rescaled power.
The only scale identities used are the physical fine/coarse cell volumes. -/
theorem FixedParents.capacity_power_bound {Child P : Type*}
    [DecidableEq Child] [DecidableEq P] (F : FixedParents Child P)
    (n : ℕ) (d r : ℝ) (hd : 0 < d) (hr : 0 < r)
    (hfd : F.fineCellVolume=d^n) (hcr : F.coarseCellVolume=r^n)
    {p : P} (hp : p ∈ F.parents) :
    (F.capacity p:ℝ)^theta ≤ (2:ℝ)^theta*(r/d)^((n:ℝ)*theta)*F.weight^theta := by
  have hu : 0 < F.weight := F.weight_pos
  have hb := F.capacity_bound p hp
  rw [hfd,hcr] at hb
  change d^n*(F.capacity p:ℝ) ≤ 2*F.weight*r^n at hb
  have hcap : (F.capacity p:ℝ) ≤ 2*F.weight*(r/d)^n := by
    rw [div_pow,← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hd n)).mpr
    nlinarith only [hb]
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (F.capacity p:ℝ)) hcap
    (by norm_num [theta] : 0 ≤ theta)
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) F.weight_pos.le] at hh
  have hpowers : ((r/d)^n)^theta=(r/d)^((n:ℝ)*theta) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
  rw [hpowers] at hh
  convert hh using 1
  ring

/-- Actual parent arithmetic pruning at source scales. The constant precedes
both scales, the rounded parent level and every prior measurable narrowing.
The closed lattice theorem is already translation- and scale-uniform, so it
applies directly to each original parent fiber without a rescaling premise. -/
theorem rounded_parent_lattice_pruning (n : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d r : ℝ) (hd : 0 < d) (hr : 0 < r),
      ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)),
      Set.InjOn Prod.snd (↑G : Set ((Fin n → ℤ) × (Fin n → ℤ))) →
      ∀ (z w : Fin n → ℝ) (level : ℕ),
      let b := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.1+z
      let v := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.2+w
      let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) hr
      ∀ I : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ,
      (∀ j, MeasurableSet (I j) ∧ I j ⊆ Set.Icc (0:ℝ) 1) →
      ∃ J : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ,
      (∀ j, MeasurableSet (J j) ∧ J j ⊆ I j) ∧
      F.portionMass volume I - eta*d^n*F.children.card ≤ F.portionMass volume J ∧
      ∀ p ∈ F.parents, ∀ t cell,
        ((F.children.filter (fun j => F.assign j=p ∧ t ∈ J j ∧
          gridIndex d (segmentPoint (b j) (v j) t)=cell)).card:ℝ) ≤
          C*(r/d)^((n:ℝ)*theta)*F.weight^theta := by
  obtain ⟨C,hC,hprune⟩ := fixed_parent_lattice_pruning_portions n eta heta
  refine ⟨C*(2:ℝ)^theta,by positivity,?_⟩
  intro d r hd hr G hinj z w level
  dsimp only
  let b := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.1+z
  let v := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.2+w
  let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) hr
  intro I hI
  have hs : F.children ⊆ G := ParentLevel.selected_subset G (RoundedParentLevel.assign r b v) level
  obtain ⟨J,hJ,hmass,hcap⟩ := hprune d hd F (hinj.mono hs) z w I hI
  refine ⟨J,hJ,hmass,?_⟩
  intro p hp t cell
  have hpowers := F.capacity_power_bound n d r hd hr rfl rfl hp
  have hh := (hcap p t cell).trans (mul_le_mul_of_nonneg_left hpowers hC.le)
  convert hh using 1
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.FixedParents.capacity_power_bound
#print axioms KakeyaTwoScale.rounded_parent_lattice_pruning
