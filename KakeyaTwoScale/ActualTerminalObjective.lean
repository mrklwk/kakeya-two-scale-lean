module
public import KakeyaTwoScale.ActualIndexedDegreeObjective
public import KakeyaTwoScale.ArchiveMultilinearPower

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive

/-- The actual terminal analytic estimate with its exact optimizer objective.
The root is explicitly normalized to one grain and incoming product one.
No analytic or degree-objective certificate is supplied as a premise. -/
theorem exists_terminal_degree_objective (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃ C : ℝ, 0≤C ∧
    ∀ {A B Lh a t b c J s : ℕ} {T O : Type} [DecidableEq T] [DecidableEq O]
      {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T (Fin (n+1)→ℤ) O}
      {U : ℝ} {fuel : ℕ},
    ∀ (H : ActualBufferedArchive k A B Lh a t T (Fin (n+1)→ℤ) O N I 1 U fuel),
      b+c=n+1 →
      HEq I.Q (fun z : Fin (n+1)→ℤ =>
        (WithLp.ofLp ⁻¹' gridCell I.δ z : Set (EuclideanSpace ℝ (Fin (n+1))))) →
      (∀y∈I.Y₀, ∀y'∈I.Y₀, I.cube y=I.cube y' → I.tube y=I.tube y' → y=y') →
      I.alpha=1/((k-1:ℕ):ℝ) → (I.W.grains I.cube).card=1 →
      (∀j, 0≤N j) → 1≤U → (∀j, (I.W.count j:ℝ)≤U*(N j*1)) →
      ∀ θ : ℝ, 0≤θ →
      (∀y∈I.W.tuples, θ≤tupleWedgeVolume (fun j => I.W.axis j (I.W.parent y j))) →
      ∀ (m : ℕ), b=m+k → ∀ (r : ℕ) (hr : r≤H.drops), r ≤ m →
      θ*(tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/H.loss)^(k-1) ≤
        C*(H.entryAt r hr).upper^k*(∏j, N j)*
          Real.exp (-degreeObjectiveLog m r (fun i => Real.log (H.stageDegrees[i]?.getD 1))) := by
  classical
  obtain ⟨C,hC,hmain⟩ := exists_archive_multilinear_ledger n k hk hkn
  refine ⟨C^(k-1)*2^k,by positivity,?_⟩
  intro A B Lh a t b c J s T O _ _ N I U fuel H hn hQ hinj hα hgrain hN hU hcount θ hθ hw m hb r hr hrm
  let E := H.entryAt r hr
  have hE : E∈H.countLedger := H.entryAt_mem r hr
  have hX : E.snapshot∈H.snapshots := by
    rw [←H.countLedger_snapshots]
    exact List.mem_map.mpr ⟨E,hE,rfl⟩
  have hG : (0:ℝ)<(E.snapshot.state.grains I.cube).card := by
    exact_mod_cast Finset.card_pos.mpr ((H.snapshots_certified _ hX).1.image _)
  have hpos := H.countLedger_positive (by norm_num : (0:ℝ)<1) hU E hE
  have hmass : 0≤tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/H.loss := by
    apply div_nonneg _ H.loss_pos.le
    exact Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hraw := hmain H hn hQ hinj hα hcount θ hθ hw E hE
  have hraw' : θ^(1/((k-1:ℕ):ℝ))*(tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/H.loss) ≤
      C*(E.snapshot.state.grains I.cube).card*
        (∏j, (2*E.upper*E.prefixProduct)*N j/(E.snapshot.state.grains I.cube).card)^(1/((k-1:ℕ):ℝ)) := by
    convert hraw using 1
    congr 2
    apply Finset.prod_congr rfl
    intro j _
    ring
  have hp := multilinear_grain_budget_power hk θ _ C _ (2*E.upper*E.prefixProduct) N hθ hmass hC hG
    (mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) hpos.2)) hpos.1.le) hN hraw'
  have hratio := H.entryAt_degree_objective m hb r hr hrm
  rw [hgrain,Nat.cast_one,one_pow,div_one,one_mul] at hratio
  apply hp.trans_eq
  calc
    _ = (C^(k-1)*2^k)*E.upper^k*(∏j, N j)*
        (E.prefixProduct^k/(E.snapshot.state.grains I.cube).card) := by rw [mul_pow,mul_pow]; ring
    _ = _ := by rw [hratio]

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_terminal_degree_objective
