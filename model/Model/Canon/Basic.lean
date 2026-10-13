import Model.Minimal

/-!
# Canonicity: closed syntax at the stages of the cube category

A closed term at stage `k` is typed in the context `k; 1; []`. A cube map `g : Hom k' k` has a
syntactic representative `tyOf g` (an interval substitution, by definability), and restricting a
closed term along `g` is substituting `tyOf g`. The value of a closed term is its denotation at
the identity environment (`semK`), natural along restrictions by soundness.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m n : ℕ}

/-- The identity environment at stage `k`: the de Bruijn index `i` is the coordinate `k - 1 - i`
(so that `(idEnv k).ext = idEnv (k + 1)`: lines bind index `0`, the last coordinate). -/
def idEnv (k : ℕ) : IEnv k := fun i => if h : i < k then DM.var ⟨k - 1 - i, by omega⟩ else DM.zero k

/-- The (irrelevant) term environment of closed terms. -/
def γ0 (k : ℕ) : ℕ → V := fun _ => emptyC k

/-- The value of a closed term at stage `k`. -/
def semK (S : Sig) (k : ℕ) (t : Tm) : V := sem S t k (idEnv k) (γ0 k)

/-- A point read in de Bruijn indices. -/
def Pt.rev (p : Pt k) : ℕ → M4 := fun i => if h : i < k then p ⟨k - 1 - i, by omega⟩ else I.M4.zero

theorem idEnv_fn (k : ℕ) (i : ℕ) (p : Pt k) : (idEnv k i).fn p = Pt.rev p i := by
  unfold idEnv Pt.rev; split <;> simp

theorem ival_idEnv_fn (r : I) (p : Pt k) : (ival (idEnv k) r).fn p = r.eval (Pt.rev p) := by
  simp only [ival.fn, idEnv_fn]

theorem idEnv_ext (k : ℕ) : (idEnv k).ext = idEnv (k + 1) := by
  funext i
  cases i with
  | zero => simp [IEnv.ext, idEnv]; rfl
  | succ i =>
    apply DM.ext; funext p
    simp only [IEnv.ext, DM.restr_fn, idEnv_fn, Pt.rev]
    by_cases h : i < k
    · rw [dif_pos h, dif_pos (by omega)]
      simp [Hom.app, Hom.wk]
      congr 1; ext; simp; omega
    · rw [dif_neg h, dif_neg (by omega)]

theorem γ0_restr (g : Hom k' k) : TEnv.restr (γ0 k) g = γ0 k' := by
  funext x; simp [TEnv.restr, γ0, res_emptyC]

theorem isPoint_idEnv (S : Sig) (k : ℕ) : IsPoint S .one [] k (idEnv k) (γ0 k)
  where
    cof := by show (ival (idEnv k) .one).holds; rw [ival_one]; rfl
    typ x A h := by simp [Ctx.lookup] at h
    kv _ := isKV_mkKV (fun _ _ => emptyDatum)

/-! ### Syntactic representatives of cube maps -/

/-- The de Bruijn reading of a term over coordinates. -/
def revSub (k : ℕ) : ℕ → I := fun n => .var (k - 1 - n)

/-- A syntactic interval substitution representing `g`. -/
def tyOf (g : Hom k' k) : ℕ → I := fun j =>
  if h : j < k then (Classical.choose (g ⟨k - 1 - j, by omega⟩).defn).subst (revSub k') else .zero

theorem tyOf_scoped (g : Hom k' k) (j : ℕ) : (tyOf g j).Scoped k' := by
  unfold tyOf; split
  · rename_i h
    have hs := (Classical.choose_spec (g ⟨k - 1 - j, by omega⟩).defn).1
    generalize Classical.choose (g ⟨k - 1 - j, by omega⟩).defn = r at hs ⊢
    induction r <;> simp_all [I.subst, I.Scoped, revSub]
    omega
  · trivial

theorem ival_tyOf (g : Hom k' k) (j : ℕ) : ival (idEnv k') (tyOf g j) = (idEnv k).restr g j := by
  apply DM.ext; funext p
  rw [ival_idEnv_fn]
  simp only [IEnv.restr, DM.restr_fn]
  unfold tyOf; split
  · rename_i h
    rw [idEnv_fn, Pt.rev, dif_pos h]
    obtain ⟨hs, he⟩ := Classical.choose_spec (g ⟨k - 1 - j, by omega⟩).defn
    rw [Cof.eval_subst]
    simp only [Hom.app]
    rw [he]
    apply Cof.eval_congr hs
    intro n hn
    simp only [revSub, I.eval, Pt.rev, Pt.ext, dif_pos (by omega : k' - 1 - n < k'), dif_pos hn]
    congr 1; ext; simp; omega
  · rename_i h
    rw [idEnv_fn, Pt.rev, dif_neg h]; rfl

theorem env_tyOf (g : Hom k' k) : (fun i => ival (idEnv k') (tyOf g i)) = (idEnv k).restr g :=
  funext (ival_tyOf g)

variable (hW : WfSig S)
include hW

/-- Typing of closed terms is stable under interval substitutions. -/
theorem HasTy.isub {t A : Tm} (ht : HasTy S k .one [] t A) (τ : ℕ → I) (hτ : ∀ i < k, (τ i).Scoped k') :
    HasTy S k' .one [] (t.subst .var τ) (A.subst .var τ) := by
  have hS := sigClosed_of_wfSig hW
  have h0 := spec_to_minimal hW ht
  refine minimal_to_spec ((sub_ty hS h0).2.1 ⟨hτ, trivial, ?_, fun x A h => by simp [Ctx.lookup] at h,
    Wf0.nil trivial⟩)
  show I.Entails .one .one
  exact I.entails_refl _

theorem EqTm.isub {t u A : Tm} (ht : EqTm S k .one [] t u A) (τ : ℕ → I) (hτ : ∀ i < k, (τ i).Scoped k') :
    EqTm S k' .one [] (t.subst .var τ) (u.subst .var τ) (A.subst .var τ) := by
  have hS := sigClosed_of_wfSig hW
  have h0 := spec_to_minimal_eq hW ht
  refine minimal_to_spec_eq ((sub_eq hS h0).2 ⟨hτ, trivial, ?_, fun x A h => by simp [Ctx.lookup] at h,
    Wf0.nil trivial⟩)
  show I.Entails .one .one
  exact I.entails_refl _

/-- The value of a restricted closed term is the restricted value. -/
theorem semK_isub {t A : Tm} (ht : HasTy S k .one [] t A) (g : Hom k' k) :
    semK S k' (t.subst .var (tyOf g)) = res g (semK S k t) := by
  have hok := sigOK_of_wfSig _ S rfl hW
  have hnat := ((sound_ty hok ht).2.2.2 k (idEnv k) (γ0 k) (isPoint_idEnv S k)).2.1 k' g
  unfold semK
  rw [show t.subst .var (tyOf g) = t.dsubst (tyOf g) from rfl, sem_dsubst, env_tyOf, ← γ0_restr g, hnat]

end

end Model.Canon
