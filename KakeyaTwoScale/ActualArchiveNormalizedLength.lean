module
public import KakeyaTwoScale.ActualArchiveGeometricMassToLength

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive

/-- Actual root joint bands cancel their common tuple scale. The effective
length is V*μ*δ/(∏N)^(1/k). Every literal ledger entry, including the root,
uses the same dimension-only grid constant chosen before all finite data. -/
theorem exists_archive_joint_band_normalized_length (n : ℕ) :
    ∃ Bgrid : ℕ, 0<Bgrid ∧
    ∀ {k A B Lh a t b c J s : ℕ} {T O : Type} [DecidableEq T] [DecidableEq O],
    ∀ {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T (Fin n→ℤ) O}
      {P U : ℝ} {fuel : ℕ},
    ∀ (H : ActualBufferedArchive k A B Lh a t T (Fin n→ℤ) O N I P U fuel),
      b+c=n →
      HEq I.Q (fun z : Fin n→ℤ => (WithLp.ofLp ⁻¹' gridCell I.δ z : Set (EuclideanSpace ℝ (Fin n)))) →
      (∀ y∈I.Y₀, ∀ z∈I.Y₀, I.cube y=I.cube z → I.tube y=I.tube z → y=z) →
      1/(k:ℝ)≤I.alpha → (∀ j, 0<N j) → 0<P → 1≤U →
      (∀ j, (I.W.count j:ℝ)≤U*(N j*P)) →
    ∀ (μ Ccap : ℝ), 0<μ → 0≤Ccap →
      (∀ q∈I.cubes, μ^k ≤ (ParentLevel.capacity I.W.tuples I.cube q:ℝ)) →
      (∀ q∈I.cubes, (ParentLevel.capacity I.W.tuples I.cube q:ℝ) ≤ Ccap*μ^k) →
    ∀ E∈H.countLedger,
      (∀ Lmax : ℝ, (∀ j, E.snapshot.state.length I.δ j≤Lmax) →
        ((I.cubes.card:ℝ)*μ*I.δ)/(∏ j, N j)^(1/(k:ℝ)) ≤
          (Bgrid:ℝ)*Ccap^(I.alpha-1/(k:ℝ))*(H.loss*E.upper)*Lmax*E.prefixProduct) ∧
      (∀ Cstar : ℝ, (∀ j, E.snapshot.state.length I.δ j≤Cstar*I.δ) →
        (((I.cubes.card:ℝ)*μ*I.δ)/(∏ j, N j)^(1/(k:ℝ)))/I.δ ≤
          (Bgrid:ℝ)*Ccap^(I.alpha-1/(k:ℝ))*(H.loss*E.upper)*Cstar*E.prefixProduct) := by
  obtain ⟨Bgrid,hB,raw⟩ := exists_archive_geometric_mass_to_length_ledger n
  refine ⟨Bgrid,hB,?_⟩
  intro k A B Lh a t b c J s T O _ _ N I P U fuel H hn hQ hinj hp hN hP hU hcount μ Ccap hμ hC hlo hhi E hE
  have hmass : (I.cubes.card:ℝ)*(μ^k)^I.alpha ≤
      tupleCubeMass I.W.tuples I.cube I.cubes I.alpha := by
    calc
      _ = ∑ q ∈ I.cubes, (μ^k)^I.alpha := by simp
      _ ≤ _ := Finset.sum_le_sum (fun q hq =>
        Real.rpow_le_rpow (pow_nonneg hμ.le _) (hlo q hq) I.exponent_pos.le)
  have hgeo : 0<(∏ j, N j)^(1/(k:ℝ)) :=
    Real.rpow_pos_of_pos (Finset.prod_pos (fun j _ => hN j)) _
  have main (Lmax : ℝ) (hL : ∀ j, E.snapshot.state.length I.δ j≤Lmax) :
      ((I.cubes.card:ℝ)*μ*I.δ)/(∏ j, N j)^(1/(k:ℝ)) ≤
        (Bgrid:ℝ)*Ccap^(I.alpha-1/(k:ℝ))*(H.loss*E.upper)*Lmax*E.prefixProduct := by
    have hr := raw H hn hQ hinj hp (fun j => (hN j).le) hP hU hcount
      (Ccap*μ^k) (mul_nonneg hC (pow_nonneg hμ.le _)) hhi E hE Lmax hL
    have hm := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hmass H.loss_pos.le) I.width_pos.le
    have hh := hm.trans hr
    have hh' : ((I.cubes.card:ℝ)*I.δ)*(μ^k)^I.alpha ≤
        ((Bgrid:ℝ)*Lmax*E.upper*E.prefixProduct*(∏ j, N j)^(1/(k:ℝ))*H.loss)*
          (Ccap*μ^k)^(I.alpha-1/(k:ℝ)) := by
      have ht := (div_le_iff₀ H.loss_pos).mp (show
          ((I.cubes.card:ℝ)*(μ^k)^I.alpha*I.δ)/H.loss ≤
            (Bgrid:ℝ)*(Ccap*μ^k)^(I.alpha-1/(k:ℝ))*Lmax*E.upper*E.prefixProduct*
              (∏ j, N j)^(1/(k:ℝ)) by
        simpa only [div_mul_eq_mul_div] using hh)
      convert ht using 1 <;> ring
    have hc := root_tuple_scale_cancel I.families_pos hμ hC hh'
    apply (div_le_iff₀ hgeo).mpr
    convert hc using 1 <;> ring
  refine ⟨main,?_⟩
  intro Cstar hshort
  apply (div_le_iff₀ I.width_pos).mpr
  convert main (Cstar*I.δ) hshort using 1; ring

/-- Select the actual first-short snapshot (or the final snapshot when no
short level occurs), and recover its literal prefix ledger. The short-case
prefix-product bound also covers r=0; no lower-budget or positive-depth
premise enters. A long exhausted endpoint is deliberately not called short. -/
theorem exists_first_short_joint_band_bound (n : ℕ) :
    ∃ Bgrid : ℕ, 0<Bgrid ∧
    ∀ {k A B Lh a t b c J s : ℕ} {T O : Type} [DecidableEq T] [DecidableEq O],
    ∀ {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T (Fin n→ℤ) O}
      {P U : ℝ} {fuel : ℕ},
    ∀ (H : ActualBufferedArchive k A B Lh a t T (Fin n→ℤ) O N I P U fuel),
      b+c=n →
      HEq I.Q (fun z : Fin n→ℤ => (WithLp.ofLp ⁻¹' gridCell I.δ z : Set (EuclideanSpace ℝ (Fin n)))) →
      (∀ y∈I.Y₀, ∀ z∈I.Y₀, I.cube y=I.cube z → I.tube y=I.tube z → y=z) →
      1/(k:ℝ)≤I.alpha → (∀ j, 0<N j) → 0<P → 1≤U →
      (∀ j, (I.W.count j:ℝ)≤U*(N j*P)) →
    ∀ (μ Ccap : ℝ), 0<μ → 0≤Ccap →
      (∀ q∈I.cubes, μ^k ≤ (ParentLevel.capacity I.W.tuples I.cube q:ℝ)) →
      (∀ q∈I.cubes, (ParentLevel.capacity I.W.tuples I.cube q:ℝ) ≤ Ccap*μ^k) →
    ∀ Cstar : ℝ, ∃ r : ℕ, ∃ E : BufferedCountSnapshot k T (Fin n→ℤ) O,
      r≤H.drops ∧ E∈H.countLedger ∧ E.snapshot=H.snapshotAt r ∧
      (r=H.drops ∨ ∀ j, E.snapshot.state.length I.δ j≤Cstar*I.δ) ∧
      (∀ i<r, ∃ j, Cstar*I.δ<(H.snapshotAt i).state.length I.δ j) ∧
      (∀ i≤r, E.snapshot.state.tuples⊆(H.snapshotAt i).state.tuples) ∧
      ((∀ j, E.snapshot.state.length I.δ j≤Cstar*I.δ) →
      (((I.cubes.card:ℝ)*μ*I.δ)/(∏ j, N j)^(1/(k:ℝ)))/I.δ ≤
        (Bgrid:ℝ)*Ccap^(I.alpha-1/(k:ℝ))*(H.loss*E.upper)*Cstar*E.prefixProduct) := by
  obtain ⟨Bgrid,hB,main⟩ := exists_archive_joint_band_normalized_length n
  refine ⟨Bgrid,hB,?_⟩
  intro k A B Lh a t b c J s T O _ _ N I P U fuel H hn hQ hinj hp hN hP hU hcount μ Ccap hμ hC hlo hhi Cstar
  obtain ⟨r,hr,hstop,hbefore,hsub,_hterm,_hmass⟩ := H.exists_first_short_snapshot Cstar
  obtain ⟨E,hE,hEq⟩ := H.snapshot_exists_countLedger _ (H.snapshotAt_mem r hr)
  refine ⟨r,E,hr,hE,hEq,?_,hbefore,?_,?_⟩
  · rw [hEq]; exact hstop
  · rw [hEq]; exact hsub
  · exact (main H hn hQ hinj hp hN hP hU hcount μ Ccap hμ hC hlo hhi E hE).2 Cstar

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_archive_joint_band_normalized_length

#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_first_short_joint_band_bound
