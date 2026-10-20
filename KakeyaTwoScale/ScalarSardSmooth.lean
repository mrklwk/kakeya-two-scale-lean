module
public import KakeyaTwoScale.CriticalJetHypersurface
public import KakeyaTwoScale.FlatJetImageNull

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace KakeyaTwoScale

private theorem nonflat_stratum_image_null {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (S : Set E) (j : ℕ)
    (hf : ∀ x ∈ S, ContDiffAt ℝ ∞ f x)
    (hcrit : ∀ x ∈ S, fderiv ℝ f x=0)
    (hz : ∀ x ∈ S, iteratedFDeriv ℝ j f x=0)
    (hn : ∀ x ∈ S, iteratedFDeriv ℝ (j+1) f x≠0)
    (ih : ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℝ K]
      [FiniteDimensional ℝ K], Module.finrank ℝ K < Module.finrank ℝ E →
      ∀ (g : K → ℝ) (T : Set K), (∀ t ∈ T, ContDiffAt ℝ ∞ g t) →
        (∀ t ∈ T, fderiv ℝ g t=0) → volume (g '' T)=0) :
    volume (f '' S)=0 := by
  classical
  have hlocal : ∀ a : S, ∃ W : Set E, IsOpen W ∧ (a:E) ∈ W ∧
      volume (f '' (S ∩ W))=0 := by
    intro a
    obtain ⟨h,hha,hDh,hzh,hsm⟩ := exists_critical_jet_hypersurface f a j
      (hf a a.property) (hz a a.property) (hn a a.property)
    obtain ⟨φ,U,W,hU,hU0,hW,haW,hφ0,hφh,hcov,hφsm,hdim⟩ :=
      exists_smooth_hypersurface_sard_chart h a ((hsm a (hf a a.property)).of_le (by simp)) hDh
    let T := {t | t ∈ U ∧ φ t ∈ S}
    have hφ : ∀ t ∈ T, ContDiffAt ℝ ∞ φ t := fun t ht =>
      hφsm t ht.1 (hsm _ (hf _ ht.2))
    have hg : ∀ t ∈ T, ContDiffAt ℝ ∞ (f ∘ φ) t := fun t ht =>
      (hf _ ht.2).comp t (hφ t ht)
    have hgc : ∀ t ∈ T, fderiv ℝ (f ∘ φ) t=0 := by
      intro t ht
      rw [fderiv_comp t ((hf _ ht.2).differentiableAt (by simp))
        ((hφ t ht).differentiableAt (by simp)),hcrit _ ht.2]
      rfl
    have hnull := ih (fderiv ℝ h (a:E)).ker (by omega) (f ∘ φ) T hg hgc
    refine ⟨W,hW,haW,measure_mono_null ?_ hnull⟩
    rintro y ⟨x,⟨hx,hxW⟩,rfl⟩
    obtain ⟨t,ht,he⟩ := hcov x hxW ((hzh x (hz x hx)).trans hha.symm)
    exact ⟨t,⟨ht,by simpa only [he] using hx⟩,by simp only [Function.comp_apply,he]⟩
  choose W hW haW hnW using hlocal
  let V : S → Set S := fun a => Subtype.val ⁻¹' W a
  have hV : ∀ a : S, V a ∈ 𝓝 a := fun a =>
    ((hW a).preimage continuous_subtype_val).mem_nhds (haW a)
  obtain ⟨I,hIc,hcover⟩ := TopologicalSpace.countable_cover_nhds hV
  let : Countable I := hIc.to_subtype
  have hnull : volume (⋃ a : I, f '' (S ∩ W a.val))=0 :=
    measure_iUnion_null (fun a => hnW a.val)
  apply measure_mono_null _ hnull
  rintro y ⟨x,hx,rfl⟩
  have hc : (⟨x,hx⟩ : S) ∈ ⋃ a ∈ I, V a := by rw [hcover]; trivial
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp hc
  exact mem_iUnion.mpr ⟨⟨a,ha⟩,x,⟨hx,hxa⟩,rfl⟩

private theorem adjacent_nonzero_jet {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (x : E)
    (h1 : iteratedFDeriv ℝ 1 f x=0) (k : ℕ) (hk : 1≤k)
    (hne : iteratedFDeriv ℝ k f x≠0) :
    ∃ j, iteratedFDeriv ℝ j f x=0 ∧ iteratedFDeriv ℝ (j+1) f x≠0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : k=0
    · subst k; exact False.elim (hne h1)
    by_cases hz : iteratedFDeriv ℝ k f x=0
    · exact ⟨k,hz,hne⟩
    · exact ih (by omega) hz

/-- Scalar smooth Sard on arbitrary subsets of a finite-dimensional real inner
product space. Only pointwise smoothness on S is required. -/
theorem scalar_sard_of_contDiffAt {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (S : Set E)
    (hf : ∀ x ∈ S, ContDiffAt ℝ ∞ f x)
    (hcrit : ∀ x ∈ S, fderiv ℝ f x=0) : volume (f '' S)=0 := by
  classical
  suffices hall : ∀ n : ℕ, ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E], Module.finrank ℝ E=n →
      ∀ (f : E → ℝ) (S : Set E), (∀ x ∈ S, ContDiffAt ℝ ∞ f x) →
        (∀ x ∈ S, fderiv ℝ f x=0) → volume (f '' S)=0 by
    exact hall _ E rfl f S hf hcrit
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ _ hdim f S hf hc
    let A := {x | x ∈ S ∧ ∀ j, 1≤j → j≤n → iteratedFDeriv ℝ j f x=0}
    let B := fun j : ℕ => {x | x ∈ S ∧ iteratedFDeriv ℝ j f x=0 ∧
      iteratedFDeriv ℝ (j+1) f x≠0}
    have hA : volume (f '' A)=0 := flat_jet_image_volume_zero_of_contDiffAt f A n
      (by omega) (fun x hx => hf x hx.1) (fun x hx => hx.2)
    have hB : ∀ j, volume (f '' B j)=0 := by
      intro j
      apply nonflat_stratum_image_null f (B j) j (fun x hx => hf x hx.1)
        (fun x hx => hc x hx.1) (fun x hx => hx.2.1) (fun x hx => hx.2.2)
      intro K _ _ _ hK g T hg hgc
      exact ih (Module.finrank ℝ K) (by omega) K rfl g T hg hgc
    have hnull : volume (f '' A ∪ ⋃ j, f '' B j)=0 :=
      measure_union_null hA (measure_iUnion_null hB)
    apply measure_mono_null _ hnull
    rintro y ⟨x,hx,rfl⟩
    by_cases ha : x ∈ A
    · exact Or.inl ⟨x,ha,rfl⟩
    have hn : ∃ j, 1≤j ∧ j≤n ∧ iteratedFDeriv ℝ j f x≠0 := by
      simpa only [A,mem_ofPred_eq,hx,true_and,not_forall,exists_prop] using ha
    obtain ⟨k,hk,_,hkne⟩ := hn
    have h1 : iteratedFDeriv ℝ 1 f x=0 := by
      ext v
      simp only [iteratedFDeriv_one_apply,hc x hx,zero_apply]
    obtain ⟨j,hj,hj1⟩ := adjacent_nonzero_jet f x h1 k hk hkne
    exact Or.inr (mem_iUnion.mpr ⟨j,x,⟨hx,hj,hj1⟩,rfl⟩)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.scalar_sard_of_contDiffAt
