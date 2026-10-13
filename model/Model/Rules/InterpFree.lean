import Model.Rules.Basic

/-!
# The denotation of a term depends only on its free variables
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

/-- `γ` and `γ'` agree on the free variables of `t`. -/
def AgreeFree (t : Tm) (γ γ' : ℕ → V) : Prop := ∀ x, t.freeIn x = true → γ x = γ' x

theorem AgreeFree.restr {t : Tm} {γ γ' : ℕ → V} (h : AgreeFree t γ γ') (f : Hom k m) :
    AgreeFree t (TEnv.restr γ f) (TEnv.restr γ' f) := fun x hx => by simp [TEnv.restr, h x hx]

theorem AgreeFree.sub {t s : Tm} {γ γ' : ℕ → V} (h : AgreeFree t γ γ') (hs : ∀ x, s.freeIn x = true → t.freeIn x = true) :
    AgreeFree s γ γ' := fun x hx => h x (hs x hx)

theorem AgreeFree.cons {t B : Tm} {γ γ' : ℕ → V} (h : AgreeFree t γ γ')
    (hs : ∀ x, B.freeIn (x + 1) = true → t.freeIn x = true) (a : V) :
    AgreeFree B (TEnv.cons γ a) (TEnv.cons γ' a) := by
  intro x hx
  cases x with
  | zero => rfl
  | succ x => simp [TEnv.cons, h x (hs x hx)]

theorem interp_congr_free (cst : SigV) (uc : ℕ → ℕ → V) (good : ℕ → V → Prop) :
    ∀ (t : Tm) (m : ℕ) (ρ : IEnv m) (γ γ' : ℕ → V), AgreeFree t γ γ' →
      interp cst uc good t m ρ γ = interp cst uc good t m ρ γ' := by
  intro t
  induction t with
  | var x => intro m ρ γ γ' hg; exact hg x (by simp [Tm.freeIn])
  | const _ | univ _ | abort | tnil => intros; rfl
  | pi A B iA iB | sigma A B iA iB | lam A B iA iB =>
    intro m ρ γ γ' hg
    have eA := iA m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx])
    have eB : ∀ k (f : Hom k m) a, interp cst uc good B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a) =
        interp cst uc good B k (ρ.restr f) (TEnv.cons (TEnv.restr γ' f) a) := fun k f a =>
      iB k _ _ _ ((hg.restr f).cons (fun x hx => by simp [Tm.freeIn, hx]) a)
    simp only [interp, eA, eB]
  | app A B iA iB =>
    intro m ρ γ γ' hg
    have eA := iA m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx])
    have hB : AgreeFree B γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have eB : ∀ k (f : Hom k m), interp cst uc good B k (ρ.restr f) (TEnv.restr γ f) =
        interp cst uc good B k (ρ.restr f) (TEnv.restr γ' f) := fun k f => iB k _ _ _ (hB.restr f)
    simp only [interp, eA, eB, iB m ρ γ γ' hB]
  | pair A B iA iB | tcons A B iA iB =>
    intro m ρ γ γ' hg
    simp only [interp, iA m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx]),
      iB m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx])]
  | fst p ip | snd p ip =>
    intro m ρ γ γ' hg
    simp only [interp, ip m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx])]
  | papp p r ip =>
    intro m ρ γ γ' hg
    simp only [interp, ip m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx])]
  | ipi A iA | plam A iA =>
    intro m ρ γ γ' hg
    have hA : AgreeFree A γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have e : ∀ k (g : Hom k (m + 1)), interp cst uc good A k (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ (Hom.wk m)) g) =
        interp cst uc good A k (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ' (Hom.wk m)) g) := fun k g =>
      iA k _ _ _ ((hA.restr _).restr g)
    simp only [interp, e, iA (m + 1) _ _ _ (hA.restr _)]
  | path A a b iA ia ib =>
    intro m ρ γ γ' hg
    have hA : AgreeFree A γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have e : ∀ k (g : Hom k (m + 1)), interp cst uc good A k (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ (Hom.wk m)) g) =
        interp cst uc good A k (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ' (Hom.wk m)) g) := fun k g =>
      iA k _ _ _ ((hA.restr _).restr g)
    simp only [interp, e, iA (m + 1) _ _ _ (hA.restr _), ia m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx]),
      ib m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx])]
  | split φ t ψ u it iu =>
    intro m ρ γ γ' hg
    simp only [interp, it m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx]),
      iu m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx])]
  | transp A φ a iA ia =>
    intro m ρ γ γ' hg
    have hA : AgreeFree A γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have ha : AgreeFree a γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have e : ∀ k (g : Hom k (m + 1)), interp cst uc good A k (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ (Hom.wk m)) g) =
        interp cst uc good A k (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ' (Hom.wk m)) g) := fun k g =>
      iA k _ _ _ ((hA.restr _).restr g)
    have ea : ∀ k (f : Hom k m), interp cst uc good a k (ρ.restr f) (TEnv.restr γ f) =
        interp cst uc good a k (ρ.restr f) (TEnv.restr γ' f) := fun k f => ia k _ _ _ (ha.restr f)
    simp only [interp, e, ea, iA (m + 1) _ _ _ (hA.restr _), ia m ρ γ γ' ha]
  | hcomp A φ u a iA iu ia =>
    intro m ρ γ γ' hg
    have hA : AgreeFree A γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have hu : AgreeFree u γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have ha : AgreeFree a γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have e : ∀ k (h : Hom k m) r, interp cst uc good u k ((ρ.restr h).cons r) (TEnv.restr γ h) =
        interp cst uc good u k ((ρ.restr h).cons r) (TEnv.restr γ' h) := fun k h r => iu k _ _ _ (hu.restr h)
    have eA : ∀ k (f : Hom k m), interp cst uc good A k (ρ.restr f) (TEnv.restr γ f) =
        interp cst uc good A k (ρ.restr f) (TEnv.restr γ' f) := fun k f => iA k _ _ _ (hA.restr f)
    have ea : ∀ k (f : Hom k m), interp cst uc good a k (ρ.restr f) (TEnv.restr γ f) =
        interp cst uc good a k (ρ.restr f) (TEnv.restr γ' f) := fun k f => ia k _ _ _ (ha.restr f)
    simp only [interp, e, eA, ea, iA m ρ γ γ' hA, ia m ρ γ γ' ha]
  | glue A φ T e iA iT ie =>
    intro m ρ γ γ' hg
    have hA : AgreeFree A γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have hT : AgreeFree T γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have he : AgreeFree e γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have eT : ∀ k (f : Hom k m), interp cst uc good T k (ρ.restr f) (TEnv.restr γ f) =
        interp cst uc good T k (ρ.restr f) (TEnv.restr γ' f) := fun k f => iT k _ _ _ (hT.restr f)
    have ee : ∀ k (f : Hom k m), interp cst uc good e k (ρ.restr f) (TEnv.restr γ f) =
        interp cst uc good e k (ρ.restr f) (TEnv.restr γ' f) := fun k f => ie k _ _ _ (he.restr f)
    have eT2 : ∀ k (f : Hom k m) n' (g : Hom n' k), interp cst uc good T n' ((ρ.restr f).restr g)
        (TEnv.restr (TEnv.restr γ f) g) = interp cst uc good T n' ((ρ.restr f).restr g)
        (TEnv.restr (TEnv.restr γ' f) g) := fun k f n' g => iT n' _ _ _ ((hT.restr f).restr g)
    have ee2 : ∀ k (f : Hom k m) n' (g : Hom n' k), interp cst uc good e n' ((ρ.restr f).restr g)
        (TEnv.restr (TEnv.restr γ f) g) = interp cst uc good e n' ((ρ.restr f).restr g)
        (TEnv.restr (TEnv.restr γ' f) g) := fun k f n' g => ie n' _ _ _ ((he.restr f).restr g)
    simp only [interp, eT, ee, eT2, ee2, iA m ρ γ γ' hA]
  | glueEl φ e t a ie it ia =>
    intro m ρ γ γ' hg
    have ht : AgreeFree t γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have et : ∀ k (f : Hom k m), interp cst uc good t k (ρ.restr f) (TEnv.restr γ f) =
        interp cst uc good t k (ρ.restr f) (TEnv.restr γ' f) := fun k f => it k _ _ _ (ht.restr f)
    simp only [interp, et, ie m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx]), it m ρ γ γ' ht,
      ia m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx])]
  | unglue φ e g ie ig =>
    intro m ρ γ γ' hg
    simp only [interp, ie m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx]),
      ig m ρ γ γ' (hg.sub fun x hx => by simp [Tm.freeIn, hx])]
  | data j ps ip =>
    intro m ρ γ γ' hg
    have hp : AgreeFree ps γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    simp only [interp]; congr 1; funext k f; exact ip k _ _ _ (hp.restr f)
  | con j c ps args rs ip ia =>
    intro m ρ γ γ' hg
    have hp : AgreeFree ps γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have ha : AgreeFree args γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    simp only [interp]; congr 1
    · funext k f; exact ip k _ _ _ (hp.restr f)
    · funext k f; exact ia k _ _ _ (ha.restr f)
  | elim j ps P bs t ip iP ib it =>
    intro m ρ γ γ' hg
    have hp : AgreeFree ps γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have hb : AgreeFree bs γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    have ht : AgreeFree t γ γ' := hg.sub fun x hx => by simp [Tm.freeIn, hx]
    simp only [interp]; congr 1
    · funext k f; exact ip k _ _ _ (hp.restr f)
    · funext k f a; exact iP k _ _ _ ((hg.restr f).cons (fun x hx => by simp [Tm.freeIn, hx]) a)
    · funext k f; exact ib k _ _ _ (hb.restr f)
    · funext k f; exact it k _ _ _ (ht.restr f)

end

end Model
