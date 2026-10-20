module
public import KakeyaTwoScale.ActualBufferedArchiveAncestry
public import KakeyaTwoScale.CertifiedPhysicalParentBudgets

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open BufferedArchiveSnapshot
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- Every actual pair of earlier/later archived levels has a deduplicated
parent map and per-parent axial budget, derived from constructed geometry. -/
theorem snapshots_parent_axial_budgets
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.snapshots.Pairwise (ParentAxialBudget I.δ) := by
  apply List.Pairwise.imp_of_mem ?_ H.snapshots_physical_ancestry.2
  intro S U hS hU h
  exact h.parent_axial_budget I.width_pos I.tube
    (H.snapshots_certified S hS) (H.snapshots_certified U hU)

/-- The original physical records bound every complete archived descendant
fiber, including records in old grains absent from the final tuple relation. -/
theorem snapshots_root_parent_axial_budgets
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    ∀ S∈H.snapshots, ParentAxialBudget I.δ (ofState I.W) S := by
  intro S hS
  exact (H.snapshots_physical_ancestry.1 S hS).parent_axial_budget I.width_pos I.tube
    (certified_of_valid _ _ _ _ _ _ I.valid I.nonempty) (H.snapshots_certified S hS)

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshots_parent_axial_budgets
#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshots_root_parent_axial_budgets
