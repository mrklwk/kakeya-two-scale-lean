module
public import KakeyaTwoScale.MaximalActiveFamily

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k → ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O}
    {P U : ℝ} {fuel : ℕ}

/-- Exhaustive analytic stopping on the immutable actual archive. A long
endpoint exhausts the requested horizon, including the possible zero horizon.
All earlier levels have a maximal long family. The same selected relation
retains mass and lies in every earlier relation; no marginal lower count is
transferred to it. -/
theorem exists_exhaustive_stopping_cases
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (Cstar : ℝ) (hthreshold : I.δ ≤ Cstar * I.δ) :
    ∃ r : ℕ, r ≤ H.drops ∧
      ((∀ j, (H.snapshotAt r).state.length I.δ j ≤ Cstar * I.δ) ∨
        (r = fuel ∧ ∃ j,
          (∀ l, (H.snapshotAt r).state.length I.δ l ≤
            (H.snapshotAt r).state.length I.δ j) ∧
          Cstar * I.δ < (H.snapshotAt r).state.length I.δ j)) ∧
      (∀ i < r, ∃ j,
        (∀ l, (H.snapshotAt i).state.length I.δ l ≤
          (H.snapshotAt i).state.length I.δ j) ∧
        Cstar * I.δ < (H.snapshotAt i).state.length I.δ j) ∧
      (∀ i ≤ r, (H.snapshotAt r).state.tuples ⊆ (H.snapshotAt i).state.tuples) ∧
      H.terminal.state.tuples ⊆ (H.snapshotAt r).state.tuples ∧
      tupleCubeMass I.W.tuples I.cube I.cubes I.alpha / H.loss ≤
        tupleCubeMass (H.snapshotAt r).state.tuples I.cube I.cubes I.alpha := by
  classical
  obtain ⟨r, hr, hstop, hbefore, hsub, hterm, hmass⟩ :=
    H.exists_first_short_snapshot Cstar
  refine ⟨r, hr, ?_, ?_, hsub, hterm, hmass⟩
  · by_cases hs : ∀ j, (H.snapshotAt r).state.length I.δ j ≤ Cstar * I.δ
    · exact Or.inl hs
    · have he : r = H.drops := hstop.resolve_right hs
      have hlong : ∃ j, Cstar * I.δ < (H.snapshotAt r).state.length I.δ j := by
        simpa only [not_forall, not_le] using hs
      have hfuel : H.drops = fuel := by
        rcases H.exhausted_or_all_short with hfuel | hfrozen
        · exact hfuel
        · exfalso
          obtain ⟨j, hj⟩ := hlong
          rw [he, H.snapshotAt_last] at hj
          simp only [FrozenGeometryState.length, hfrozen j, pow_zero, mul_one] at hj
          exact (not_lt_of_ge hthreshold) hj
      exact Or.inr ⟨he.trans hfuel,
        (H.snapshotAt r).state.exists_maximal_long_family I.δ (Cstar * I.δ) hlong⟩
  · intro i hi
    exact (H.snapshotAt i).state.exists_maximal_long_family I.δ (Cstar * I.δ)
      (hbefore i hi)

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_exhaustive_stopping_cases
