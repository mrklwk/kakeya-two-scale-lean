module
public import KakeyaTwoScale.LatticePruning
public import KakeyaTwoScale.PortionPruning

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Apply the closed arithmetic pruning theorem simultaneously to the original
fixed parent fibers. Constants precede the scale and the parent assignment.
The parent capacities and assignments are never recomputed after deletion. -/
theorem fixed_parent_lattice_pruning (n : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ {P : Type*} [DecidableEq P]
        (F : FixedParents ((Fin n → ℤ) × (Fin n → ℤ)) P),
      Set.InjOn Prod.snd (↑F.children : Set ((Fin n → ℤ) × (Fin n → ℤ))) →
      ∀ z w : Fin n → ℝ, ∃ J : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ,
      (∀ j, MeasurableSet (J j) ∧ J j ⊆ Set.Icc (0:ℝ) 1) ∧
      (∀ p, ∑ j ∈ F.children.filter (fun j => F.assign j = p),
        volume.real (Set.Icc (0:ℝ) 1 \ J j) ≤ eta*(F.capacity p : ℝ)) ∧
      ∀ p t k, ((F.children.filter (fun j => F.assign j = p ∧ t ∈ J j ∧
        gridIndex r (segmentPoint (latticePoint r j.1+z)
          (latticePoint r j.2+w) t)=k)).card:ℝ) ≤ C*(F.capacity p:ℝ)^theta := by
  obtain ⟨C,hC,hprune⟩ := lattice_multiplicity_pruning n eta heta
  refine ⟨C,hC,?_⟩
  intro r hr P _ F hinj z w
  let G := fun p => F.children.filter (fun j => F.assign j=p)
  have hex : ∀ p, ∃ J : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ,
      (∀ j, MeasurableSet (J j) ∧ J j ⊆ Set.Icc (0:ℝ) 1) ∧
      (1-eta)*((G p).card:ℝ) ≤ ∑ j ∈ G p, volume.real (J j) ∧
      ∀ t k, (((G p).filter (fun j => t ∈ J j ∧ gridIndex r
        (segmentPoint (latticePoint r j.1+z) (latticePoint r j.2+w) t)=k)).card:ℝ) ≤
        C*((G p).card:ℝ)^theta := by
    intro p
    by_cases hp : (G p).Nonempty
    · exact hprune r hr (G p) hp (hinj.mono (Finset.filter_subset _ _)) z w
    · have he := Finset.not_nonempty_iff_eq_empty.mp hp
      refine ⟨fun _ => ∅,fun _ => ⟨MeasurableSet.empty,Set.empty_subset _⟩,?_,?_⟩
      · simp [he]
      · intro t k
        simp only [he,Finset.filter_empty,Finset.card_empty,Nat.cast_zero]
        positivity
  choose J hm hmass hcap using hex
  let I := fun j => J (F.assign j) j
  refine ⟨I,fun j => hm (F.assign j) j,?_,?_⟩
  · intro p
    have he (j) (hj : j ∈ G p) : I j = J p j := by
      dsimp [I]; rw [(Finset.mem_filter.mp hj).2]
    have hvol (j) : volume.real (Set.Icc (0:ℝ) 1 \ J p j) = 1-volume.real (J p j) := by
      rw [measureReal_sdiff (hm p j).2 (hm p j).1 (by simp)]
      simp
    change (∑ j ∈ G p, volume.real (Set.Icc (0:ℝ) 1 \ I j)) ≤ eta*((G p).card:ℝ)
    simp_rw [Finset.sum_congr rfl (fun j hj => congrArg (fun S => volume.real (Set.Icc (0:ℝ) 1 \ S)) (he j hj))]
    simp_rw [hvol]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    nlinarith [hmass p]
  · intro p t k
    have he : F.children.filter (fun j => F.assign j=p ∧ t ∈ I j ∧
        gridIndex r (segmentPoint (latticePoint r j.1+z) (latticePoint r j.2+w) t)=k) =
        (G p).filter (fun j => t ∈ J p j ∧ gridIndex r
          (segmentPoint (latticePoint r j.1+z) (latticePoint r j.2+w) t)=k) := by
      ext j
      simp only [Finset.mem_filter,G]
      dsimp [I]
      by_cases hj : F.assign j=p <;> simp [hj]
    rw [he]
    exact hcap p t k

/-- Arithmetic deletion can be applied after an arbitrary measurable narrowing.
Its loss is charged to original capacities, while its cap holds at every
height and in every cell, without an almost-everywhere exception. -/
theorem fixed_parent_lattice_pruning_portions (n : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ {P : Type*} [DecidableEq P]
        (F : FixedParents ((Fin n → ℤ) × (Fin n → ℤ)) P),
      Set.InjOn Prod.snd (↑F.children : Set ((Fin n → ℤ) × (Fin n → ℤ))) →
      ∀ z w : Fin n → ℝ,
      ∀ I : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ,
      (∀ j, MeasurableSet (I j) ∧ I j ⊆ Set.Icc (0:ℝ) 1) →
      ∃ J : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ,
      (∀ j, MeasurableSet (J j) ∧ J j ⊆ I j) ∧
      F.portionMass volume I - eta*F.fineCellVolume*F.children.card ≤
        F.portionMass volume J ∧
      ∀ p t k, ((F.children.filter (fun j => F.assign j = p ∧ t ∈ J j ∧
        gridIndex r (segmentPoint (latticePoint r j.1+z)
          (latticePoint r j.2+w) t)=k)).card:ℝ) ≤ C*(F.capacity p:ℝ)^theta := by
  obtain ⟨C,hC,hprune⟩ := fixed_parent_lattice_pruning n eta heta
  refine ⟨C,hC,?_⟩
  intro r hr P _ F hinj z w I hI
  obtain ⟨J,hJ,hbudget,hcap⟩ := hprune r hr F hinj z w
  refine ⟨fun j => I j ∩ J j,fun j => ⟨(hI j).1.inter (hJ j).1,Set.inter_subset_left⟩,?_,?_⟩
  · have hfinite (j) : volume (I j) ≠ ⊤ :=
      measure_ne_top_of_subset (hI j).2 (by simp)
    have hsum : F.portionMass volume (fun j => I j ∩ J j) +
        F.portionMass volume (fun j => I j \ J j) = F.portionMass volume I := by
      unfold FixedParents.portionMass
      rw [← mul_add,← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => measureReal_inter_add_sdiff (hJ j).1 (hfinite j))
    have hb : F.portionMass volume (fun j => I j \ J j) ≤
        eta*F.fineCellVolume*F.children.card := by
      apply F.exceptional_budget volume (fun j => I j \ J j) eta
      intro p _
      apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) (hbudget p)
      exact measureReal_mono (Set.sdiff_subset_sdiff_left (hI j).2)
        (measure_ne_top_of_subset Set.sdiff_subset (by simp))
    linarith
  · intro p t k
    have hc := hcap p t k
    have hs : F.children.filter (fun j => F.assign j = p ∧ t ∈ I j ∩ J j ∧
        gridIndex r (segmentPoint (latticePoint r j.1+z) (latticePoint r j.2+w) t)=k) ⊆
      F.children.filter (fun j => F.assign j = p ∧ t ∈ J j ∧
        gridIndex r (segmentPoint (latticePoint r j.1+z) (latticePoint r j.2+w) t)=k) := by
      intro j hj
      obtain ⟨hj,hp,ht,hk⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hj,hp,ht.2,hk⟩
    have hcard := (Nat.cast_le (α:=ℝ)).mpr (Finset.card_le_card hs)
    have hh := hcard.trans (show _ ≤ C*(F.capacity p:ℝ)^theta from by
      convert hc using 1)
    convert hh using 1
    congr 2
    ext j
    simp only [Finset.mem_filter]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.fixed_parent_lattice_pruning_portions
#print axioms KakeyaTwoScale.fixed_parent_lattice_pruning
