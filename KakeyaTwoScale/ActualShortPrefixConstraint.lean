module
public import KakeyaTwoScale.ActualDegreePrefixLog
public import KakeyaTwoScale.ActualArchiveNormalizedLength

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive

/-- Actual short-prefix constraint for the numerical early-stop optimizer.
The common normalized length comes from the root joint count band, and the
prefix log comes from the literal archive ledger. All losses remain displayed. -/
theorem exists_short_prefix_log_constraint (n : ℕ) :
    ∃ Bgrid : ℕ, 0<Bgrid ∧
    ∀ {k A B Lh a t b c J s : ℕ} {T O : Type} [DecidableEq T] [DecidableEq O]
      {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T (Fin n→ℤ) O}
      {U : ℝ} {fuel : ℕ},
    ∀ (H : ActualBufferedArchive k A B Lh a t T (Fin n→ℤ) O N I 1 U fuel),
      b+c=n →
      HEq I.Q (fun z : Fin n→ℤ => (WithLp.ofLp ⁻¹' gridCell I.δ z : Set (EuclideanSpace ℝ (Fin n)))) →
      (∀y∈I.Y₀, ∀y'∈I.Y₀, I.cube y=I.cube y' → I.tube y=I.tube y' → y=y') →
      1/(k:ℝ)≤I.alpha → (∀j, 0<N j) → 1≤U →
      (∀j, (I.W.count j:ℝ)≤U*(N j*1)) →
      ∀ (μ Ccap : ℝ), 0<μ → 0<Ccap →
      (∀q∈I.cubes, μ^k≤(ParentLevel.capacity I.W.tuples I.cube q:ℝ)) →
      (∀q∈I.cubes, (ParentLevel.capacity I.W.tuples I.cube q:ℝ)≤Ccap*μ^k) →
      ∀ (r : ℕ) (hr : r≤H.drops) (Cstar : ℝ), 0<Cstar →
      (∀j, (H.snapshotAt r).state.length I.δ j≤Cstar*I.δ) →
      Real.log ((((I.cubes.card:ℝ)*μ*I.δ)/(∏j, N j)^(1/(k:ℝ)))/I.δ)-
        Real.log ((Bgrid:ℝ)*Ccap^(I.alpha-1/(k:ℝ))*(H.loss*(H.entryAt r hr).upper)*Cstar) ≤
          degreePrefixLog (fun i => Real.log (H.stageDegrees[i]?.getD 1)) r := by
  classical
  obtain ⟨Bgrid,hB,hmain⟩ := exists_archive_joint_band_normalized_length n
  refine ⟨Bgrid,hB,?_⟩
  intro k A B Lh a t b c J s T O _ _ N I U fuel H hn hQ hinj hp hN hU hcount μ Ccap hμ hC rlo rhi r hr Cstar hCstar hshort
  let E := H.entryAt r hr
  have hE : E∈H.countLedger := H.entryAt_mem r hr
  have hpositive := H.countLedger_positive (by norm_num : (0:ℝ)<1) hU E hE
  have hs : ∀j, E.snapshot.state.length I.δ j≤Cstar*I.δ := by
    rw [show E.snapshot=H.snapshotAt r from H.entryAt_snapshot r hr]
    exact hshort
  have hh := (hmain H hn hQ hinj hp hN (by norm_num) hU hcount μ Ccap hμ hC.le rlo rhi E hE).2 Cstar hs
  have hcubes : (0:ℝ)<I.cubes.card := by
    obtain ⟨y,hy⟩ := I.nonempty
    exact_mod_cast Finset.card_pos.mpr ⟨I.cube y,I.support y (I.valid.1 hy)⟩
  have hwidth := I.width_pos
  have hprod : 0<∏j, N j := Finset.prod_pos (fun j _ => hN j)
  have hleft : 0<(((I.cubes.card:ℝ)*μ*I.δ)/(∏j, N j)^(1/(k:ℝ)))/I.δ := by positivity
  have hupper : 0<E.upper := lt_of_lt_of_le zero_lt_one hpositive.2
  have hK : 0<(Bgrid:ℝ)*Ccap^(I.alpha-1/(k:ℝ))*(H.loss*E.upper)*Cstar := by
    have := H.loss_pos
    positivity
  have hlog := Real.log_le_log hleft hh
  rw [Real.log_mul hK.ne' hpositive.1.ne'] at hlog
  have he := H.entryAt_log_prefix (by norm_num : (0:ℝ)<1) r hr
  rw [Real.log_one,zero_add] at he
  rw [he] at hlog
  linarith

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_short_prefix_log_constraint
