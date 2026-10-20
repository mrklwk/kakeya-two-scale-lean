module
public import KakeyaTwoScale.PhysicalLatticeMultilinear
public import KakeyaTwoScale.FrozenGeometryState
public import KakeyaTwoScale.NonlinearTupleSelection

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Actual finite physical record relations. The only injectivity requested
is within one cube; different cubes may retain the same original tuple. -/
theorem physical_tuple_multilinear (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃ C : ℝ, 0≤C ∧ ∀ (T P : Type) [DecidableEq T] [DecidableEq P]
      (Y : Finset T) (cube : T → Fin (n+1) → ℤ) (cubes : Finset (Fin (n+1) → ℤ))
      (parent : T → Fin k → P)
      (b u : Fin k → P → EuclideanSpace ℝ (Fin (n+1))) (ell : Fin k → P → ℝ)
      (δ θ : ℝ), 0<δ → 0≤θ → (∀j t, ‖u j t‖=1) →
      (∀y∈Y, ∀y'∈Y, cube y=cube y' → parent y=parent y' → y=y') →
      (∀y∈Y, θ≤tupleWedgeVolume (fun j => u j (parent y j))) →
      (∀y∈Y, ∀j, ((WithLp.ofLp ⁻¹' gridCell δ (cube y)) ∩
        flatCylinder (b j (parent y j)) (u j (parent y j)) (ell j (parent y j)) δ).Nonempty) →
      θ^(1/((k-1:ℕ):ℝ))*tupleCubeMass Y cube cubes (1/((k-1:ℕ):ℝ)) ≤
        C*(∏j, ((Y.image (fun y => parent y j)).card:ℝ))^(1/((k-1:ℕ):ℝ)) := by
  obtain ⟨C,hC,hmain⟩ := physical_retained_lattice_multilinear n k hk hkn
  refine ⟨C,hC,?_⟩
  intro T P _ _ Y cube cubes parent b u ell δ θ hδ hθ hu hinj hw hi
  let A := fun j => Y.image (fun y => parent y j)
  let e := fun j => (A j).equivFin
  let z := fun q : Fin cubes.card => (cubes.equivFin.symm q).val
  let enc := fun (y : Y) (j : Fin k) => e j ⟨parent y.val j,Finset.mem_image.mpr ⟨y.val,y.property,rfl⟩⟩
  let R := fun q : Fin cubes.card => (Y.attach.filter (fun y => cube y.val=z q)).image enc
  have hz : Function.Injective z := fun q q' h =>
    cubes.equivFin.symm.injective (Subtype.ext h)
  have hdecode (y : Y) (j : Fin k) : ((e j).symm (enc y j)).val=parent y.val j := by simp [enc]
  have hR (q : Fin cubes.card) : (R q).card=ParentLevel.capacity Y cube (z q) := by
    rw [show (R q).card=(Y.attach.filter (fun y => cube y.val=z q)).card by
      apply Finset.card_image_iff.mpr
      intro y hy y' hy' he
      apply Subtype.ext
      apply hinj y.val y.property y'.val y'.property
      · exact (Finset.mem_filter.mp hy).2.trans (Finset.mem_filter.mp hy').2.symm
      · funext j
        have hh := congrArg (fun f => ((e j).symm (f j)).val) he
        simpa only [hdecode] using hh]
    simp only [ParentLevel.capacity]
    exact Finset.card_bij (fun y _ => y.val)
      (by intro y hy; exact Finset.mem_filter.mpr ⟨y.property,(Finset.mem_filter.mp hy).2⟩)
      (by intro y _ y' _ h; exact Subtype.ext h)
      (by intro y hy; exact ⟨⟨y,(Finset.mem_filter.mp hy).1⟩,Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,(Finset.mem_filter.mp hy).2⟩,rfl⟩)
  have hmass : (∑q : Fin cubes.card, ((R q).card:ℝ)^(1/((k-1:ℕ):ℝ)))=
      tupleCubeMass Y cube cubes (1/((k-1:ℕ):ℝ)) := by
    simp only [hR,tupleCubeMass]
    rw [←Finset.sum_attach cubes]
    exact Fintype.sum_equiv cubes.equivFin.symm _ _ (fun _ => rfl)
  have hh := hmain δ hδ cubes.card z hz (fun j => (A j).card)
    (fun j t => b j ((e j).symm t).val) (fun j t => u j ((e j).symm t).val)
    (fun j t => ell j ((e j).symm t).val) R θ (fun j t => hu j _) hθ
    (by
      intro q f hf
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hf
      simpa only [hdecode] using hw y.val y.property)
    (by
      intro q f hf j
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hf
      have hq := (Finset.mem_filter.mp hy).2
      simpa only [hdecode,←hq] using hi y.val y.property j)
  rw [hmass] at hh
  exact hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.physical_tuple_multilinear
