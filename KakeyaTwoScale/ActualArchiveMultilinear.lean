module
public import KakeyaTwoScale.ActualGrainMultilinear
public import KakeyaTwoScale.ActualArchiveGeometricMassToLength

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Gram wedge is preserved by literal physical ancestry, even across the
archive's ambient-dimension equality transports. -/
theorem BufferedArchiveSnapshot.PhysicalAncestor.wedge_eq
    {k : ℕ} {T C O : Type} {δ : ℝ} {S U : BufferedArchiveSnapshot k T C O}
    (h : BufferedArchiveSnapshot.PhysicalAncestor δ S U) (y : T) (hy : y∈U.state.tuples) :
    tupleWedgeVolume (fun j => U.state.axis j (U.state.parent y j))=
      tupleWedgeVolume (fun j => S.state.axis j (S.state.parent y j)) := by
  rcases S with ⟨n,S⟩
  rcases U with ⟨m,U⟩
  obtain ⟨h,_,_,ha,_⟩ := h
  dsimp only at h
  subst m
  exact congrArg tupleWedgeVolume (funext (ha y hy))

namespace ActualBufferedArchive

/-- Every immutable snapshot retains the constructed whole-grain balance. -/
theorem snapshots_balanced
    {k A B Lh a t b c J s : ℕ} {T Q O : Type} [DecidableEq T] [DecidableEq Q]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T Q O}
    {P U : ℝ} {fuel : ℕ}
    (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel) :
    ∀X∈H.snapshots, X.state.Balanced I.cube I.cubes I.alpha := by
  induction H with
  | zero I P U =>
    intro X hX
    rcases List.mem_singleton.mp hX with rfl
    exact I.balanced
  | short I P U hs =>
    intro X hX
    rcases List.mem_singleton.mp hX with rfl
    exact I.balanced
  | last I P U Z =>
    intro X hX
    rcases List.mem_cons.mp hX with rfl | hX
    · exact I.balanced
    · rcases List.mem_singleton.mp hX with rfl
      exact Z.balanced
  | next I P U Z hb ht tail ih =>
    intro X hX
    rcases List.mem_cons.mp hX with rfl | hX
    · exact I.balanced
    · simpa only [AmbientBufferedStageData.nextData_cube,
        AmbientBufferedStageData.nextData_cubes,AmbientBufferedStageData.nextData_alpha] using ih X hX

/-- Actual archive terminal analytic input at every immutable snapshot.
The root mass retention, physical incidence, and original wedge lower bound
are transported from the actual archive. No selected marginal lower counts
and no assumed analytic estimate appear. -/
theorem exists_archive_multilinear (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃ C : ℝ, 0≤C ∧
    ∀ {A B Lh a t b c J s : ℕ} {T O : Type} [DecidableEq T] [DecidableEq O]
      {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T (Fin (n+1)→ℤ) O}
      {P U : ℝ} {fuel : ℕ},
    ∀ (H : ActualBufferedArchive k A B Lh a t T (Fin (n+1)→ℤ) O N I P U fuel),
      b+c=n+1 →
      HEq I.Q (fun z : Fin (n+1)→ℤ =>
        (WithLp.ofLp ⁻¹' gridCell I.δ z : Set (EuclideanSpace ℝ (Fin (n+1))))) →
      (∀y∈I.Y₀, ∀y'∈I.Y₀, I.cube y=I.cube y' → I.tube y=I.tube y' → y=y') →
      I.alpha=1/((k-1:ℕ):ℝ) → ∀ θ : ℝ, 0≤θ →
      (∀y∈I.W.tuples, θ≤tupleWedgeVolume (fun j => I.W.axis j (I.W.parent y j))) →
      ∀ X∈H.snapshots,
      θ^(1/((k-1:ℕ):ℝ))*(tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/H.loss) ≤
        C*∑g∈X.state.grains I.cube,
          (∏j, ((X.state.grainRecords I.cube g j).card:ℝ))^(1/((k-1:ℕ):ℝ)) := by
  classical
  obtain ⟨C,hC,hmain⟩ := actual_grain_multilinear n k hk hkn
  refine ⟨C,hC,?_⟩
  intro A B Lh a t b c J s T O _ _ N I P U fuel H hn hQ hinj hα θ hθ hw X hX
  obtain ⟨S,hS,hvalid⟩ := H.snapshots_valid_in_coordinates (n+1) hn _ hQ X hX
  subst X
  have hsub : S.tuples⊆I.W.tuples := H.snapshots_tuples_subset _ hX
  have hwS (y) (hy : y∈S.tuples) : θ≤tupleWedgeVolume (fun j => S.axis j (S.parent y j)) := by
    have he := (H.snapshots_physical_ancestry.1 _ hX).wedge_eq y hy
    dsimp only [BufferedArchiveSnapshot.ofState] at he
    exact (hw y (hsub hy)).trans_eq he.symm
  have hm := H.terminal_mass.trans (tuple_mass_mono _ _ I.cube I.cubes
    (H.terminal_subset_every_snapshot _ hX) I.exponent_pos.le)
  have hraw := hmain T O S I.Y₀ I.cube I.tube I.cubes I.δ θ I.width_pos hθ hvalid hinj hwS
  apply le_trans _ hraw
  have hh := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hθ (1/((k-1:ℕ):ℝ)))
  simpa only [hα,BufferedArchiveSnapshot.ofState] using hh

/-- Terminal analytic input with the actual normalized prefix count ledger.
The factor 2 is the constructed grain balance, and G is the actual grain count.
The complete degree saving is retained as G times a product of 1/G budgets. -/
theorem exists_archive_multilinear_ledger (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃ C : ℝ, 0≤C ∧
    ∀ {A B Lh a t b c J s : ℕ} {T O : Type} [DecidableEq T] [DecidableEq O]
      {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T (Fin (n+1)→ℤ) O}
      {P U : ℝ} {fuel : ℕ},
    ∀ (H : ActualBufferedArchive k A B Lh a t T (Fin (n+1)→ℤ) O N I P U fuel),
      b+c=n+1 →
      HEq I.Q (fun z : Fin (n+1)→ℤ =>
        (WithLp.ofLp ⁻¹' gridCell I.δ z : Set (EuclideanSpace ℝ (Fin (n+1))))) →
      (∀y∈I.Y₀, ∀y'∈I.Y₀, I.cube y=I.cube y' → I.tube y=I.tube y' → y=y') →
      I.alpha=1/((k-1:ℕ):ℝ) →
      (∀j, (I.W.count j:ℝ)≤U*(N j*P)) →
      ∀ θ : ℝ, 0≤θ →
      (∀y∈I.W.tuples, θ≤tupleWedgeVolume (fun j => I.W.axis j (I.W.parent y j))) →
      ∀ E∈H.countLedger,
      θ^(1/((k-1:ℕ):ℝ))*(tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/H.loss) ≤
        C*(E.snapshot.state.grains I.cube).card*
          (∏j, 2*(E.upper*(N j*E.prefixProduct))/(E.snapshot.state.grains I.cube).card)^
            (1/((k-1:ℕ):ℝ)) := by
  classical
  obtain ⟨C,hC,hmain⟩ := exists_archive_multilinear n k hk hkn
  refine ⟨C,hC,?_⟩
  intro A B Lh a t b c J s T O _ _ N I P U fuel H hn hQ hinj hα hcount θ hθ hw E hE
  have hX : E.snapshot∈H.snapshots := by
    rw [←H.countLedger_snapshots]
    exact List.mem_map.mpr ⟨E,hE,rfl⟩
  apply (hmain H hn hQ hinj hα θ hθ hw E.snapshot hX).trans
  let G : ℝ := (E.snapshot.state.grains I.cube).card
  let M := fun j => 2*(E.upper*(N j*E.prefixProduct))/G
  have hsum : (∑g∈E.snapshot.state.grains I.cube,
      (∏j, ((E.snapshot.state.grainRecords I.cube g j).card:ℝ))^(1/((k-1:ℕ):ℝ))) ≤
      G*(∏j, M j)^(1/((k-1:ℕ):ℝ)) := by
    calc
      _ ≤ ∑_g∈E.snapshot.state.grains I.cube, (∏j, M j)^(1/((k-1:ℕ):ℝ)) := by
        apply Finset.sum_le_sum
        intro g hg
        apply Real.rpow_le_rpow (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) _ (by positivity)
        apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        intro j _
        have hb := ((H.snapshots_balanced E.snapshot hX g hg).2 j).2
        have hc := H.countLedger_count hcount E hE j
        exact hb.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc (by norm_num)) (Nat.cast_nonneg _))
      _ = _ := by simp [G]
  simpa only [G,M,mul_assoc] using mul_le_mul_of_nonneg_left hsum hC

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.BufferedArchiveSnapshot.PhysicalAncestor.wedge_eq
#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_archive_multilinear

#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshots_balanced
#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_archive_multilinear_ledger
