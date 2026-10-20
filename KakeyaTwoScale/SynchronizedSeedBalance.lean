module
public import KakeyaTwoScale.SynchronizedSeedUnion
public import KakeyaTwoScale.BufferedSeedMassCap

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState
attribute [local instance] Classical.propDecidable

/-- Global balancing acts on the constructed tagged union. Every surviving
record is literally a local physical record, and the lift retains its old
variety tag and its local terminal grain. -/
theorem exists_balanced_synchronized_union {n k B : ℕ} {T C O I : Type}
    [DecidableEq T] [DecidableEq C] [Fintype I] [Nonempty I]
    (S : I → FrozenGeometryState n k T C O)
    (owner : C → I) (cube : T → C) (height : Fin k → ℕ) (radius δ p : ℝ)
    (Y : Finset T) (tube : T → Fin k → O) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (cubes : Finset C) (U : FrozenGeometryState n k T C O)
    (hU : U.Valid Y cube tube Q δ)
    (old : I → U.Grain) (hold : Function.Injective old)
    (hv : ∀ i, (S i).Valid Y cube tube Q δ)
    (hne : ∀ i, (S i).tuples.Nonempty)
    (howner : ∀ i y, y ∈ (S i).tuples → owner (cube y)=i)
    (hsub : ∀ i, (S i).tuples ⊆ U.tuples)
    (hgrain : ∀ i y, y ∈ (S i).tuples → U.grain (cube y)=old i)
    (hgeom : ∀ i y, y ∈ (S i).tuples → ∀ j,
      (S i).geometry δ j ((S i).parent y j) ⊆ U.geometry δ j (U.parent y j))
    (hheight : ∀ i, (S i).height=height)
    (hradius : ∀ i, (S i).ballRadius ≤ radius)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hcubes : ∀ y ∈ Y, cube y ∈ cubes) (hbound : (Y.card:ℝ) ≤ (2:ℝ)^B) :
    ∃ (V : FrozenGeometryState n k T C O) (lift : V.Grain → Σ i, (S i).Grain),
      V.Valid Y cube tube Q δ ∧ V.Balanced cube cubes p ∧ V.tuples.Nonempty ∧
      (∀ y ∈ V.tuples, y ∈ (S (owner (cube y))).tuples) ∧
      V.height=height ∧ V.ballRadius=radius ∧
      (∀ y ∈ V.tuples, lift (V.grain (cube y))=⟨owner (cube y),(S (owner (cube y))).grain (cube y)⟩) ∧
      (∑ i, tupleCubeMass (S i).tuples cube cubes p) / (((B+1)^(k+1):ℕ):ℝ) ≤
        tupleCubeMass V.tuples cube cubes p ∧
      (∀ j, V.count j ≤ ∑ i, (S i).count j) ∧
      (∀ y ∈ V.tuples, ∀ j, V.geometry δ j (V.parent y j)=
        (S (owner (cube y))).geometry δ j ((S (owner (cube y))).parent y j)) ∧
      (∀ y ∈ V.tuples, ∀ j, V.axis j (V.parent y j)=
        (S (owner (cube y))).axis j ((S (owner (cube y))).parent y j)) := by
  classical
  let A := synchronizedUnion S owner cube height radius
  have hA := synchronizedUnion_valid S owner cube height radius δ Y tube Q U hU old hold
    hv howner hsub hgrain hgeom hheight hradius
  have hAn : A.tuples.Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty I›
    obtain ⟨y,hy⟩ := hne i
    refine ⟨y,(synchronizedUnion_mem S owner cube height radius howner y).mpr ?_⟩
    simpa only [howner i y hy] using hy
  obtain ⟨V,lift,hv',hb,hn,hs,hh,hr,hl,hm,hct,_,hg,ha⟩ :=
    exists_balanced_state (B:=B) A Y cube tube Q cubes hp hp1 hA hAn
      (fun y hy => hcubes y (hA.1 hy))
      ((by exact_mod_cast Finset.card_le_card hA.1 : (A.tuples.card:ℝ) ≤ Y.card).trans hbound)
  refine ⟨V,lift,hv',hb,hn,?_,hh,hr,hl,?_,?_,?_,ha⟩
  · exact fun y hy => (synchronizedUnion_mem S owner cube height radius howner y).mp (hs hy)
  · rwa [synchronizedUnion_mass S owner cube height radius cubes hp howner] at hm
  · exact fun j => (hct j).trans (synchronizedUnion_count S owner cube height radius howner j)
  · intro y hy j
    exact (hg y hy j).trans (synchronizedUnion_geometry S owner cube height radius δ hheight j _)

/-- The balanced tagged grain remains a subset of one original local grain;
its nonlinear mass cap therefore survives the global rebalancing. -/
theorem synchronized_grain_mass_cap {n k : ℕ} {T C O I : Type}
    [DecidableEq T] [DecidableEq C]
    (S : I → FrozenGeometryState n k T C O) (V : FrozenGeometryState n k T C O)
    (owner : C → I) (cube : T → C) (cubes : Finset C) {p : ℝ} (hp : 0 ≤ p)
    (lift : V.Grain → Σ i, (S i).Grain)
    (hmem : ∀ y ∈ V.tuples, y ∈ (S (owner (cube y))).tuples)
    (hl : ∀ y ∈ V.tuples, lift (V.grain (cube y))=⟨owner (cube y),(S (owner (cube y))).grain (cube y)⟩)
    (cap : I → ℝ)
    (hcap : ∀ i g, g ∈ (S i).grains cube → tupleCubeMass ((S i).tuples.filter fun y => (S i).grain (cube y)=g) cube cubes p ≤ cap i)
    (g : V.Grain) (hg : g ∈ V.grains cube) :
    tupleCubeMass (V.tuples.filter fun y => V.grain (cube y)=g) cube cubes p ≤ cap (lift g).1 := by
  classical
  have hactive : (lift g).2 ∈ (S (lift g).1).grains cube := by
    obtain ⟨y,hy,hyg⟩ := Finset.mem_image.mp hg
    change V.grain (cube y)=g at hyg
    have he := (hl y hy).symm
    rw [hyg] at he
    have hi : owner (cube y)=(lift g).1 := congrArg Sigma.fst he
    have hyl : y ∈ (S (lift g).1).tuples := by simpa only [hi] using hmem y hy
    refine Finset.mem_image.mpr ⟨y,hyl,?_⟩
    have he' : (⟨(lift g).1,(S (lift g).1).grain (cube y)⟩ : Σ i, (S i).Grain)=lift g := by
      exact (congrArg (fun i => (⟨i,(S i).grain (cube y)⟩ : Σ i, (S i).Grain)) hi).symm.trans he
    exact eq_of_heq (Sigma.mk.inj he').2
  apply (tuple_mass_mono ((S (lift g).1).tuples.filter fun y => (S (lift g).1).grain (cube y)=(lift g).2) _ cube cubes ?_ hp).trans
    (hcap (lift g).1 (lift g).2 hactive)
  intro y hy
  obtain ⟨hy,hyg⟩ := Finset.mem_filter.mp hy
  have he := (hl y hy).symm
  rw [hyg] at he
  have hi : owner (cube y)=(lift g).1 := congrArg Sigma.fst he
  have hyl : y ∈ (S (lift g).1).tuples := by simpa only [hi] using hmem y hy
  apply Finset.mem_filter.mpr ⟨hyl,?_⟩
  have he' : (⟨(lift g).1,(S (lift g).1).grain (cube y)⟩ : Σ i, (S i).Grain)=lift g := by
    exact (congrArg (fun i => (⟨i,(S i).grain (cube y)⟩ : Σ i, (S i).Grain)) hi).symm.trans he
  exact eq_of_heq (Sigma.mk.inj he').2

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_balanced_synchronized_union
#print axioms KakeyaTwoScale.FrozenGeometryState.synchronized_grain_mass_cap
