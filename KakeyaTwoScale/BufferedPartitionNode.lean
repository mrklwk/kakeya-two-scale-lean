module
public import KakeyaTwoScale.OrientedWeightedBufferedPartition
public import KakeyaTwoScale.OwnedPartitionRecursion

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

variable {b c J s : ℕ} {C : Type} [DecidableEq C]
    {P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ} {D : ℕ → ℕ}
    {S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))}
    {Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))} {w : C → ℝ} {η r : ℝ}

/-- Exact cellular witnesses, retained with the same chosen partition data. -/
def BufferedCellCertificate (A : Finset C)
    (d : OrientedWeightedBufferedData (J:=J) (s:=s) P D S A Q w η r)
    (children : Finset (Finset C)) : Prop :=
  ∃ (G : Finset C) (owner : C → Fin s → Bool), G ⊆ d.selected ∧
    children=ownedOwnerCells G owner ∧
    (∀ u ∈ G, Q u ⊆ (fun x => coordinateBaseProjection (d.orientation x)) ⁻¹'
      polynomialSignCell d.q (owner u)) ∧
    (∀ u ∈ G, ∀ x ∈ Q u,
      coordinateBaseProjection (d.orientation x) ∉ thickening r (polynomialFactorZeros d.q))

def BufferedLeafCertificate (A : Finset C)
    (d : OrientedWeightedBufferedData (J:=J) (s:=s) P D S A Q w η r)
    (selected : Finset C) : Prop :=
  ∃ i : Option (Fin s), ∀ u ∈ selected, Q u ⊆ thickening (η+2*(η+r))
    ({y | rectangularPolynomialMap P y=0} ∩ {y | MvPolynomial.eval y (d.wall i)=0})

/-- Convert the actual oriented split to one recursion node, preserving the
same factors, orientation, owners, physical successor and whole original weights. -/
theorem orientedBufferedData_node (A : Finset C)
    (d : OrientedWeightedBufferedData (J:=J) (s:=s) P D S A Q w η r)
    (hw : ∀ u ∈ A, 0 ≤ w u) :
    Nonempty (OwnedPartitionNode w (2*(S.card:ℝ)) s
      (fun A => OrientedWeightedBufferedData (J:=J) (s:=s) P D S A Q w η r)
      (fun _ _ => True) BufferedCellCertificate BufferedLeafCertificate A) := by
  classical
  rcases d.alternative with ⟨G,owner,hG,hmass,hcell,havoid,hcap⟩ | ⟨G,i,hG,hmass,hcapture⟩
  · refine ⟨{
      data := d
      valid := trivial
      children := ownedOwnerCells G owner
      selected := ∅
      split := Or.inr ⟨rfl,?_,ownedOwnerCells_disjoint G owner,?_,?_⟩ }⟩
    · intro T hT
      obtain ⟨hne,label,rfl⟩ := (mem_ownedOwnerCells G owner).mp hT
      refine ⟨hne,(Finset.filter_subset _ _).trans (hG.trans d.selected_subset),?_⟩
      have ht : (∑ u ∈ d.selected, w u) ≤ ∑ u ∈ A, w u :=
        Finset.sum_le_sum_of_subset_of_nonneg d.selected_subset (fun u hu _ => hw u hu)
      have hdiv := div_le_div_of_nonneg_right ht (by positivity : 0 ≤ (2:ℝ)^s)
      change (∑ u ∈ G.filter (fun u => owner u=label), w u) ≤ _
      calc
        _ ≤ 2*((∑ u ∈ d.selected, w u)/(2:ℝ)^s) := hcap label
        _ ≤ 2*((∑ u ∈ A, w u)/(2:ℝ)^s) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ = ((2:ℝ)/2^s)*ownedCubeMass w A := by unfold ownedCubeMass; ring
    · rw [ownedOwnerCells_mass]
      exact hmass
    · exact ⟨G,owner,hG,rfl,hcell,havoid⟩
  · exact ⟨{
      data := d
      valid := trivial
      children := ∅
      selected := G
      split := Or.inl ⟨rfl,hG.trans d.selected_subset,hmass,i,hcapture⟩ }⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.orientedBufferedData_node
