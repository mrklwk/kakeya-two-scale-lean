module
public import KakeyaTwoScale.ActualArchiveLocalization
public import KakeyaTwoScale.ConcreteRootArchive

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open BufferedArchiveSnapshot

/-- The concrete root satisfies the same sum-of-lengths radius bound as all
normalized successors; positivity of the family count pays the singleton root. -/
theorem concreteRoot_radius_controlled {n k : ℕ} {O : Type}
    (Y : Finset (RootTuple n k O)) (q : ℕ) (a : Fin n→ℤ)
    (b u : O→EuclideanSpace ℝ (Fin n)) (hk : 0<k) :
    RadiusControlled (n+1) ((2:ℝ)^q)⁻¹ (ofState (concreteRootState Y q a b u)) := by
  change (2*n+6:ℝ) ≤ ((n+1:ℕ)+n+5:ℝ)*((2:ℝ)^q)⁻¹*(∑ _j : Fin k, (2:ℝ)^q)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have he : (((n+1:ℕ)+n+5:ℝ)*((2:ℝ)^q)⁻¹)*((k:ℝ)*2^q)=(2*n+6)*k := by
    push_cast
    field_simp
    ring
  rw [he]
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  nlinarith [Nat.cast_nonneg (α:=ℝ) n]

/-- Every full archived grain admits a uniform record-to-original count for
its maximal-length family. All localization, ancestry and disjointness
hypotheses are derived from the concrete construction. -/
theorem concrete_archive_grain_multiplicity {n k N q t : ℕ}
    (hn : 0<n) (hk : 0<k) (hq : 1≤q) (ht : 2≤t)
    (Y : Finset (RootTuple n k (Fin N))) (a : Fin n→ℤ)
    (b u : Fin N→EuclideanSpace ℝ (Fin n)) (hu : ∀ o, ‖u o‖=1)
    (hsep : ∀ o p, o≠p → ((2:ℝ)^q)⁻¹≤Real.arccos |inner ℝ (u o) (u p)|)
    (hinc : ∀ y∈Y, ∀ j, (rootGridCube ((2:ℝ)^q)⁻¹ y.1 ∩
      flatCylinder (b (y.2 j)) (u (y.2 j)) 1 ((2:ℝ)^q)⁻¹).Nonempty)
    (hne : (coarseRootTuples Y ((2:ℝ)^q)⁻¹ a).Nonempty)
    (alpha : ℝ) (hp : 0<alpha) (hp1 : alpha≤1)
    (drop fuel : ℕ) (normN : Fin k→ℝ) (P U : ℝ)
    (H : ActualBufferedArchive k (n+1) (((4*k+3)*n)*q) q drop t
      (RootTuple n k (Fin N)) (Fin n→ℤ) (Fin N) normN
      (concreteRootAmbient hn hk hq ht Y a b u hu hsep hinc hne alpha hp hp1) P U fuel) :
    ∀ X∈H.snapshots, ∃ h : X.dimension=n,
      let S : FrozenGeometryState n k (RootTuple n k (Fin N)) (Fin n→ℤ) (Fin N) :=
        Eq.mp (congrArg (fun d => FrozenGeometryState d k (RootTuple n k (Fin N))
          (Fin n→ℤ) (Fin N)) h) X.state
      ∀ (g : S.Grain) (j : Fin k),
        (∀ i, S.length ((2:ℝ)^q)⁻¹ i ≤ S.length ((2:ℝ)^q)⁻¹ j) →
        let F := S.grainRecords Prod.fst g j
        (F.card:ℝ) ≤ 2*((2*n+6:ℝ)*k)*((F.image (S.original j)).card:ℝ) := by
  classical
  let I := concreteRootAmbient hn hk hq ht Y a b u hu hsep hinc hne alpha hp hp1
  intro X hX
  have hlocal := H.snapshots_localized X hX
  have hrad := H.snapshots_radius_controlled (concreteRoot_radius_controlled Y q a b u hk) X hX
  have hcert := H.snapshots_certified X hX
  obtain ⟨h,hsub,hcontain,haxes,horiginal⟩ := H.snapshots_physical_ancestry.1 X hX
  rcases X with ⟨m,S⟩
  change m=n at h
  subst m
  refine ⟨rfl,?_⟩
  dsimp only
  intro g j hmax
  have hax : ∀ j r, r∈S.records j → S.axis j r=u (S.original j r) := by
    intro j r hr
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hr
    have ha : S.axis j (S.parent y j)=u (y.2 j) := haxes y hy j
    have ho : S.original j (S.parent y j)=y.2 j := hcert.2.2.1 y hy j
    simpa only [ho] using ha
  have hroot : ∀ j r, r∈S.records j → S.geometry ((2:ℝ)^q)⁻¹ j r ⊆
      flatCylinder (b (S.original j r)) (u (S.original j r)) 1 ((2:ℝ)^q)⁻¹ := by
    intro j r hr
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hr
    have hc := hcontain y hy j
    have ho : S.original j (S.parent y j)=y.2 j := hcert.2.2.1 y hy j
    rw [ho]
    change S.geometry ((2:ℝ)^q)⁻¹ j (S.parent y j) ⊆
      (concreteRootState Y q a b u).geometry ((2:ℝ)^q)⁻¹ j (y.2 j) at hc
    simpa only [concreteRootState_geometry] using hc
  have hbound := S.maximal_family_radius (n+1) ((2:ℝ)^q)⁻¹ hrad j hmax
  have hbound' : S.ballRadius ≤ ((2*n+6:ℝ)*k)*S.length ((2:ℝ)^q)⁻¹ j := by
    convert hbound using 1
    push_cast
    ring
  exact S.grain_records_le_originals Prod.fst Prod.snd ((2:ℝ)^q)⁻¹ ((2*n+6:ℝ)*k)
    (by positivity) (by positivity) b u hu hcert hax hroot hlocal g j hbound'

end KakeyaTwoScale
#print axioms KakeyaTwoScale.concreteRoot_radius_controlled
#print axioms KakeyaTwoScale.concrete_archive_grain_multiplicity
