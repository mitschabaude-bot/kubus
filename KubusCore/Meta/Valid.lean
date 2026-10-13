import KubusCore.Meta.Inversion

/-!
# Metatheory: validity

Types of typed terms are types (or universes), given presupposition for the minimal
judgments (`Presup0`) and typed definitions in the signature (`SigTyped0`).
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- `A` is a type: typed at some universe, or a universe. -/
def IsTyp (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (A : Tm) : Prop :=
  (∃ l, HasTy0 S Ψ Φ Γ A (univ l)) ∨ ∃ l, A = univ l

/-- Presupposition for the minimal equality judgment. -/
def Presup0 (S : Sig) : Prop :=
  ∀ {Ψ Φ Γ t u A}, EqTm0 S Ψ Φ Γ t u A → HasTy0 S Ψ Φ Γ t A ∧ HasTy0 S Ψ Φ Γ u A

/-- The definitions of the signature are typed (in the minimal judgments). -/
def SigTyped0 (S : Sig) : Prop :=
  ∀ (k : Nat) (t A : Tm), S[k]? = some (.defn t A) →
    (∃ l, HasTy0 S 0 .one [] A (univ l)) ∧ HasTy0 S 0 .one [] t A

theorem IsTyp.restrict {Ψ Φ Φ' Γ A} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) :
    IsTyp S Ψ Φ Γ A → IsTyp S Ψ Φ' Γ A
  | .inl ⟨l, h⟩ => .inl ⟨l, HasTy0.restrict hs he h⟩
  | .inr h => .inr h

/-- A closed judgment holds in every well-formed context. -/
theorem HasTy0.ofEmpty (hS : SigClosed S) {t A Ψ Φ Γ} (h : HasTy0 S 0 .one [] t A)
    (hw : Wf0 S Ψ Φ Γ) : HasTy0 S Ψ Φ Γ t A := by
  have hR : TyRen S 0 .one [] Ψ Φ Γ id id :=
    { inj := fun i j h => h, bound := fun i hi => (Nat.not_lt_zero _ hi).elim
      hscoped := scoped_of_wf hw, ent := ent_one _, look := fun x A hx => by cases hx
      wf := wfAll_of_wf hS hw }
  have := (ren_ty hS h).2 hR
  have e : ∀ u : Tm, u.subst (rS id) (rI id) = u := fun u => subst_var u
  rwa [e, e] at this

theorem EqTm0.ofEmpty (hS : SigClosed S) {t u A Ψ Φ Γ} (h : EqTm0 S 0 .one [] t u A)
    (hw : Wf0 S Ψ Φ Γ) : EqTm0 S Ψ Φ Γ t u A := by
  have hR : TyRen S 0 .one [] Ψ Φ Γ id id :=
    { inj := fun i j h => h, bound := fun i hi => (Nat.not_lt_zero _ hi).elim
      hscoped := scoped_of_wf hw, ent := ent_one _, look := fun x A hx => by cases hx
      wf := wfAll_of_wf hS hw }
  have := (ren_eq hS h).2 hR
  have e : ∀ u : Tm, u.subst (rS id) (rI id) = u := fun u => subst_var u
  rwa [e, e, e] at this

/-- The types of a well-formed context are types. -/
theorem lookup_typed (hS : SigClosed S) {Ψ Φ} : ∀ {Γ : Ctx}, Wf0 S Ψ Φ Γ → ∀ {x A}, Γ.lookup x = some A →
    ∃ l, HasTy0 S Ψ Φ Γ A (univ l)
  | [], _, _, _, hx => by cases hx
  | B :: Γ, .cons hB, x, A, hx => by
    cases x with
    | zero =>
      simp only [Ctx.lookup, Option.some.injEq] at hx; subst hx
      exact ⟨_, HasTy0.wk hS hB hB⟩
    | succ x =>
      simp only [Ctx.lookup, Option.map_eq_some_iff] at hx
      obtain ⟨A0, hA0, rfl⟩ := hx
      obtain ⟨l, h⟩ := lookup_typed hS (wf_of_ty hB) hA0
      exact ⟨l, HasTy0.wk hS hB h⟩

section
variable (hS : SigClosed S) (hP : Presup0 S) (hT : SigTyped0 S)
include hS hP hT

theorem valid_ty {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → IsTyp S Ψ Φ Γ A
  | .var h0 h1 => .inl (lookup_typed hS h0 h1)
  | .conv _ h1 => .inl ⟨_, (hP h1).2⟩
  | .restrict hs he h2 => (valid_ty h2).restrict hs he
  | .const h0 h1 => .inl ((hT _ _ _ h1).1.elim fun l h => ⟨l, HasTy0.ofEmpty hS h h0⟩)
  | .univ _ _ => .inr ⟨_, rfl⟩
  | .cumul _ _ => .inr ⟨_, rfl⟩
  | .pi _ _ => .inr ⟨_, rfl⟩
  | .lam h0 _ => .inl ⟨_, h0⟩
  | .app h0 h1 => by
    rcases valid_ty h0 with ⟨l, h⟩ | ⟨l, h⟩
    · exact .inl ⟨l, HasTy0.subst hS (HasTy0.piCod hS h) h1⟩
    · cases h
  | .sigma _ _ => .inr ⟨_, rfl⟩
  | .pair h0 _ _ => .inl ⟨_, h0⟩
  | .fst h0 => by
    rcases valid_ty h0 with ⟨l, h⟩ | ⟨l, h⟩
    · exact .inl ⟨l, HasTy0.sigmaDom hS h⟩
    · cases h
  | .snd h0 => by
    rcases valid_ty h0 with ⟨l, h⟩ | ⟨l, h⟩
    · exact .inl ⟨l, HasTy0.subst hS (HasTy0.sigmaCod hS h) (HasTy0.fst h0)⟩
    · cases h
  | .path _ _ _ => .inr ⟨_, rfl⟩
  | .plam h0 _ _ _ => .inl ⟨_, h0⟩
  | .papp h0 h1 => by
    rcases valid_ty h0 with ⟨l, h⟩ | ⟨l, h⟩
    · exact .inl ⟨l, HasTy0.dsubst hS (HasTy0.pathLine hS h) h1⟩
    · cases h
  | .ipi _ _ => .inr ⟨_, rfl⟩
  | .ilam h0 _ => .inl ⟨_, h0⟩
  | .iapp h0 h1 => by
    rcases valid_ty h0 with ⟨l, h⟩ | ⟨l, h⟩
    · exact .inl ⟨l, HasTy0.dsubst hS (HasTy0.ipiLine hS h) h1⟩
    · cases h
  | .split _ _ _ h3 _ _ _ => .inl ⟨_, h3⟩
  | .abort _ h1 => .inl ⟨_, h1⟩
  | .transp h0 _ _ _ => .inl ⟨_, HasTy0.dsubst hS h0 trivial⟩
  | .hcomp h0 _ _ _ _ => .inl ⟨_, h0⟩
  | .glue _ _ _ _ => .inr ⟨_, rfl⟩
  | .glueEl h0 _ _ _ _ => .inl ⟨_, h0⟩
  | .unglue _ h1 _ _ => .inl ⟨_, h1⟩
  | .data _ _ _ => .inr ⟨_, rfl⟩
  | .con _ _ _ h3 _ _ _ _ => .inl ⟨_, h3⟩
  | .elim _ _ _ _ h4 _ _ _ _ h9 => .inl ⟨_, HasTy0.subst hS h4 h9⟩

end

end KubusCore.Meta
