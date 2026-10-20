module
public import KakeyaTwoScale.ActualBufferedArchiveAncestry

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- Algebraic data of the actual immutable state, including the equation
family which a physical-only snapshot intentionally does not retain. -/
structure PolynomialArchiveSnapshot (k : ℕ) (T C O : Type) where
  dimension : ℕ
  codimension : ℕ
  degree : ℕ
  state : FrozenGeometryState dimension k T C O
  equations : state.Grain → Fin codimension → MvPolynomial (Fin dimension) ℝ
  radius : ℝ

namespace PolynomialArchiveSnapshot
variable {k : ℕ} {T C O : Type}

def physical (S : PolynomialArchiveSnapshot k T C O) : BufferedArchiveSnapshot k T C O :=
  ⟨S.dimension,S.state⟩

def zeroSet (S : PolynomialArchiveSnapshot k T C O) (g : S.state.Grain) :
    Set (EuclideanSpace ℝ (Fin S.dimension)) :=
  {x | rectangularPolynomialMap (S.equations g) x=0}

def ofData {b c A B Lh J s : ℕ} [DecidableEq T] [DecidableEq C]
    (I : AmbientBufferedStageData b c k A B Lh J s T C O) : PolynomialArchiveSnapshot k T C O :=
  ⟨b+c,c,J,I.W,I.P,I.K⟩

def ofStage {b c A B Lh J s a : ℕ} [DecidableEq T] [DecidableEq C]
    (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} (Z : ActualNormalizedBufferedStage I.toInput N P U a) :
    PolynomialArchiveSnapshot k T C O :=
  ⟨b+c,c+1,I.successorDegree,Z.state,Z.equations,I.toInput.R+3⟩

/-- Algebraic ancestry supplies a single ancestor grain for each current
grain, as well as a zero-set inclusion for every represented current grain. -/
def Ancestor (cube : T→C) (S U : PolynomialArchiveSnapshot k T C O) : Prop :=
  ∃ h : U.dimension=S.dimension,
    U.state.tuples ⊆ S.state.tuples ∧
    ∃ parent : U.state.Grain→S.state.Grain,
      (∀ y∈U.state.tuples, parent (U.state.grain (cube y))=S.state.grain (cube y)) ∧
      (∀ g∈U.state.grains cube, ∀ x∈U.zeroSet g,
        (h ▸ x : EuclideanSpace ℝ (Fin S.dimension)) ∈ S.zeroSet (parent g))

theorem Ancestor.refl (cube : T→C) (S : PolynomialArchiveSnapshot k T C O) :
    Ancestor cube S S := ⟨rfl,fun _ h=>h,id,fun _ _=>rfl,fun _ _ _ hx=>hx⟩

theorem Ancestor.trans {cube : T→C} {S U V : PolynomialArchiveSnapshot k T C O}
    (hSU : Ancestor cube S U) (hUV : Ancestor cube U V) : Ancestor cube S V := by
  classical
  rcases S with ⟨n,c,D,S,P,R⟩
  rcases U with ⟨m,d,E,U,Q,R'⟩
  rcases V with ⟨l,e,F,V,H,R''⟩
  rcases hSU with ⟨h,hs,p,hp,hzero⟩
  rcases hUV with ⟨h',hs',p',hp',hzero'⟩
  dsimp only at h h'
  subst m
  subst l
  refine ⟨rfl,hs'.trans hs,p ∘ p',?_,?_⟩
  · intro y hy
    exact (congrArg p (hp' y hy)).trans (hp y (hs' hy))
  · intro g hg
    have hm : p' g∈U.grains cube := by
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hg
      change p' (V.grain (cube y))∈U.grains cube
      rw [hp' y hy]
      exact Finset.mem_image_of_mem _ (hs' hy)
    intro x hx
    exact hzero (p' g) hm x (hzero' g hg x hx)

/-- All analytic uses of these data can access genuine degree, rank and
capture conclusions. No neighborhood-volume/count estimate is a field. -/
def Sound (δ : ℝ) (cube : T→C) (S : PolynomialArchiveSnapshot k T C O) : Prop :=
  (∀ g∈S.state.grains cube, ∀ i, (S.equations g i).totalDegree≤S.degree) ∧
  (∀ g∈S.state.grains cube, ∀ x, rectangularPolynomialMap (S.equations g) x=0 →
    (fderiv ℝ (rectangularPolynomialMap (S.equations g)) x).range=⊤) ∧
  (∀ y∈S.state.tuples, ∀ j, S.state.geometry δ j (S.state.parent y j) ⊆
    thickening (S.radius*δ) (S.zeroSet (S.state.grain (cube y))))

theorem ofData_sound {b c A B Lh J s : ℕ} [DecidableEq T] [DecidableEq C]
    (I : AmbientBufferedStageData b c k A B Lh J s T C O) : Sound I.δ I.cube (ofData I) :=
  ⟨I.degree,I.regular,I.capture⟩

theorem ofStage_sound {b c A B Lh J s a : ℕ} [DecidableEq T] [DecidableEq C]
    (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} (Z : ActualNormalizedBufferedStage I.toInput N P U a) :
    Sound I.δ I.cube (ofStage I Z) :=
  ⟨fun g _ i=>Z.degrees g i,Z.regular,Z.capture⟩

theorem ofStage_ancestor {b c A B Lh J s a : ℕ} [DecidableEq T] [DecidableEq C]
    (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} (Z : ActualNormalizedBufferedStage I.toInput N P U a) :
    Ancestor I.cube (ofData I) (ofStage I Z) := by
  classical
  refine ⟨rfl,Z.tuples_subset,Z.oldGrain,Z.old_grain,?_⟩
  intro g hg x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hg
  change rectangularPolynomialMap (I.P (Z.oldGrain (Z.state.grain (I.cube y)))) x=0
  have hold : Z.oldGrain (Z.state.grain (I.cube y))=I.W.grain (I.cube y) := Z.old_grain y hy
  rw [hold]
  apply PiLp.ext
  intro i
  have hz := congrArg (fun v : EuclideanSpace ℝ (Fin (c+1))=>v i.succ) hx
  have he : Z.equations (Z.state.grain (I.cube y)) i.succ=I.P (I.W.grain (I.cube y)) i :=
    (Z.old_equations y hy i).trans (I.toInput_back_polynomial (I.W.grain (I.cube y)) i)
  change MvPolynomial.eval (fun j=>x j) (I.P (I.W.grain (I.cube y)) i)=0
  change MvPolynomial.eval (fun j=>x j) (Z.equations (Z.state.grain (I.cube y)) i.succ)=0 at hz
  rwa [he] at hz

end PolynomialArchiveSnapshot
end KakeyaTwoScale
#print axioms KakeyaTwoScale.PolynomialArchiveSnapshot.Ancestor.trans
#print axioms KakeyaTwoScale.PolynomialArchiveSnapshot.ofData_sound
#print axioms KakeyaTwoScale.PolynomialArchiveSnapshot.ofStage_sound
#print axioms KakeyaTwoScale.PolynomialArchiveSnapshot.ofStage_ancestor
