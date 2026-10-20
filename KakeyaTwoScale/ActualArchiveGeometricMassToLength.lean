module
public import KakeyaTwoScale.ActualGeometricMassToLength
public import KakeyaTwoScale.ActualArchiveMassToLength
public import KakeyaTwoScale.ActualArchiveAnalyticSelection
public import KakeyaTwoScale.ActualBufferedArchiveAncestry
public import KakeyaTwoScale.ActualArchiveCountLedger

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive

/-- Repaired maximal-length inequality on every actual snapshot. The root
fiber cap is inherited by subset; retained mass and validity are extracted
from the archive, not supplied as snapshot premises. -/
theorem exists_archive_geometric_mass_to_length (n : ℕ) :
    ∃ Bgrid : ℕ, 0<Bgrid ∧
    ∀ {k A B Lh a t b c J s : ℕ} {T O : Type} [DecidableEq T] [DecidableEq O],
    ∀ {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T (Fin n→ℤ) O}
      {P U : ℝ} {fuel : ℕ},
    ∀ (H : ActualBufferedArchive k A B Lh a t T (Fin n→ℤ) O N I P U fuel),
      b+c=n →
      HEq I.Q (fun z : Fin n→ℤ => (WithLp.ofLp ⁻¹' gridCell I.δ z : Set (EuclideanSpace ℝ (Fin n)))) →
      (∀ y∈I.Y₀, ∀ z∈I.Y₀, I.cube y=I.cube z → I.tube y=I.tube z → y=z) →
      1/(k:ℝ)≤I.alpha →
    ∀ M : ℝ, 0≤M →
      (∀ q∈I.cubes, (ParentLevel.capacity I.W.tuples I.cube q:ℝ)≤M) →
    ∀ X∈H.snapshots, ∀ Lmax : ℝ, (∀ j, X.state.length I.δ j≤Lmax) →
      (tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/H.loss)*I.δ ≤
        (Bgrid:ℝ)*M^(I.alpha-1/(k:ℝ))*Lmax*(∏ j, (X.state.count j:ℝ))^(1/(k:ℝ)) := by
  classical
  obtain ⟨Bgrid,hB,hmain⟩ := exists_actual_geometric_mass_to_length n
  refine ⟨Bgrid,hB,?_⟩
  intro k A B Lh a t b c J s T O _ _ N I P U fuel H hn hQ hinj hp M hM hcap X hX Lmax hmax
  obtain ⟨S,hS,hvalid⟩ := H.snapshots_valid_in_coordinates n hn _ hQ X hX
  subst X
  have hnonempty : S.tuples.Nonempty := (H.snapshots_certified _ hX).1
  have hsub : S.tuples⊆I.W.tuples := H.snapshots_tuples_subset _ hX
  have hcapS (q) (hq : q∈I.cubes) : (ParentLevel.capacity S.tuples I.cube q:ℝ)≤M := by
    have hh : ParentLevel.capacity S.tuples I.cube q≤ParentLevel.capacity I.W.tuples I.cube q :=
      Finset.card_le_card (Finset.filter_subset_filter _ hsub)
    exact (by exact_mod_cast hh : (ParentLevel.capacity S.tuples I.cube q:ℝ)≤
      (ParentLevel.capacity I.W.tuples I.cube q:ℝ)).trans (hcap q hq)
  have hm := H.terminal_mass.trans (tuple_mass_mono _ _ I.cube I.cubes
    (H.terminal_subset_every_snapshot _ hX) I.exponent_pos.le)
  exact (mul_le_mul_of_nonneg_right hm I.width_pos.le).trans
    (hmain S hnonempty I.Y₀ I.cube I.tube I.cubes I.δ I.width_pos hvalid I.support hinj
      I.families_pos I.alpha M hp hM hcapS Lmax hmax)

/-- The repaired bridge with the actual P_i and U_i at every literal ledger
entry. It includes frozen families and zero-horizon archives. No degree/count
upper bound for a selected marginal, and no individual μ_j, is introduced. -/
theorem exists_archive_geometric_mass_to_length_ledger (n : ℕ) :
    ∃ Bgrid : ℕ, 0<Bgrid ∧
    ∀ {k A B Lh a t b c J s : ℕ} {T O : Type} [DecidableEq T] [DecidableEq O],
    ∀ {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T (Fin n→ℤ) O}
      {P U : ℝ} {fuel : ℕ},
    ∀ (H : ActualBufferedArchive k A B Lh a t T (Fin n→ℤ) O N I P U fuel),
      b+c=n →
      HEq I.Q (fun z : Fin n→ℤ => (WithLp.ofLp ⁻¹' gridCell I.δ z : Set (EuclideanSpace ℝ (Fin n)))) →
      (∀ y∈I.Y₀, ∀ z∈I.Y₀, I.cube y=I.cube z → I.tube y=I.tube z → y=z) →
      1/(k:ℝ)≤I.alpha → (∀ j, 0≤N j) → 0<P → 1≤U →
      (∀ j, (I.W.count j:ℝ)≤U*(N j*P)) →
    ∀ M : ℝ, 0≤M →
      (∀ q∈I.cubes, (ParentLevel.capacity I.W.tuples I.cube q:ℝ)≤M) →
    ∀ E∈H.countLedger, ∀ Lmax : ℝ, (∀ j, E.snapshot.state.length I.δ j≤Lmax) →
      (tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/H.loss)*I.δ ≤
        (Bgrid:ℝ)*M^(I.alpha-1/(k:ℝ))*Lmax*E.upper*E.prefixProduct*(∏ j, N j)^(1/(k:ℝ)) := by
  classical
  obtain ⟨Bgrid,hB,hmain⟩ := exists_archive_geometric_mass_to_length n
  refine ⟨Bgrid,hB,?_⟩
  intro k A B Lh a t b c J s T O _ _ N I P U fuel H hn hQ hinj hp hN hP hU hcount M hM hcap E hE Lmax hmax
  have hX : E.snapshot∈H.snapshots := by
    rw [←H.countLedger_snapshots]
    exact List.mem_map.mpr ⟨E,hE,rfl⟩
  have hpositive := H.countLedger_positive hP hU E hE
  have hL : 0≤Lmax := by
    have hlen : 0≤E.snapshot.state.length I.δ ⟨0,I.families_pos⟩ := by
      unfold FrozenGeometryState.length
      exact mul_nonneg I.width_pos.le (pow_nonneg (by norm_num) _)
    exact hlen.trans (hmax ⟨0,I.families_pos⟩)
  have hgeo := geometric_mean_le_count_budget I.families_pos
    (fun j => (E.snapshot.state.count j:ℝ)) N E.upper E.prefixProduct
    (fun j => Nat.cast_nonneg _) hN (by linarith [hpositive.2]) hpositive.1.le
    (H.countLedger_count hcount E hE)
  have hraw := hmain H hn hQ hinj hp M hM hcap E.snapshot hX Lmax hmax
  apply hraw.trans
  have hh := mul_le_mul_of_nonneg_left hgeo
    (show 0≤(Bgrid:ℝ)*M^(I.alpha-1/(k:ℝ))*Lmax by positivity)
  convert hh using 1
  ring

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_archive_geometric_mass_to_length
#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_archive_geometric_mass_to_length_ledger
