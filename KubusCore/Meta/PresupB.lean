import KubusCore.Meta.KanU

/-!
# Metatheory: auxiliary notions for presupposition

`IsTypB`: a type is typed at a universe, or is a universe of bounded level. The bound makes the
levels of all type equations bounded (`IsTypB.lvl`), so that conversion chains can be collapsed
into one equation by cumulativity.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- `A` is a type: typed at some universe, or a universe of level at most `maxLevel`. -/
def IsTypB (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (A : Tm) : Prop :=
  (∃ l, HasTy0 S Ψ Φ Γ A (univ l)) ∨ ∃ l, A = univ l ∧ l ≤ maxLevel

/-- Generation for universes: only levels below `maxLevel` are typed. -/
theorem gen_univ {Ψ Φ Γ s T} (h : HasTy0 S Ψ Φ Γ s T) {l} (hs : s = .univ l) : l + 1 ≤ maxLevel :=
  match h with
  | .var _ _ => by cases hs
  | .conv h0 h1 => gen_univ h0 hs
  | .restrict h0 h1 h2 => gen_univ h2 hs
  | .const _ _ => by cases hs
  | .univ h0 h1 => by cases hs; exact h0
  | .cumul h0 h1 => gen_univ h1 hs
  | .pi _ _ => by cases hs
  | .lam _ _ => by cases hs
  | .app _ _ => by cases hs
  | .sigma _ _ => by cases hs
  | .pair _ _ _ => by cases hs
  | .fst _ => by cases hs
  | .snd _ => by cases hs
  | .path _ _ _ => by cases hs
  | .plam _ _ _ _ => by cases hs
  | .papp _ _ => by cases hs
  | .ipi _ _ => by cases hs
  | .ilam _ _ => by cases hs
  | .iapp _ _ => by cases hs
  | .split _ _ _ _ _ _ _ => by cases hs
  | .abort _ _ => by cases hs
  | .transp _ _ _ _ => by cases hs
  | .hcomp _ _ _ _ _ => by cases hs
  | .glue _ _ _ _ => by cases hs
  | .glueEl _ _ _ _ _ => by cases hs
  | .unglue _ _ _ _ => by cases hs
  | .data _ _ _ => by cases hs
  | .con _ _ _ _ _ _ _ _ => by cases hs
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases hs

theorem IsTypB.lvl {Ψ Φ Γ l} : IsTypB S Ψ Φ Γ (univ l) → l ≤ maxLevel
  | .inl ⟨_, h⟩ => Nat.le_of_succ_le (gen_univ h rfl)
  | .inr ⟨_, h, hl⟩ => by cases h; exact hl

theorem IsTypB.restrict {Ψ Φ Φ' Γ A} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) :
    IsTypB S Ψ Φ Γ A → IsTypB S Ψ Φ' Γ A
  | .inl ⟨l, h⟩ => .inl ⟨l, HasTy0.restrict hs he h⟩
  | .inr h => .inr h

theorem IsTypB.toIsTyp {Ψ Φ Γ A} : IsTypB S Ψ Φ Γ A → IsTyp S Ψ Φ Γ A
  | .inl h => .inl h
  | .inr ⟨l, h, _⟩ => .inr ⟨l, h⟩

/-! ## Collapsing conversion chains -/

theorem EqTm0.lift {Ψ Φ Γ X Y m} (e : EqTm0 S Ψ Φ Γ X Y (Tm.univ m)) :
    ∀ {k}, m ≤ k → k ≤ maxLevel → EqTm0 S Ψ Φ Γ X Y (Tm.univ k)
  | k, hmk, hk => by
    induction k with
    | zero => cases Nat.le_zero.1 hmk; exact e
    | succ k ih =>
      rcases Nat.lt_or_eq_of_le hmk with h | h
      · exact EqTm0.cumul hk (ih (Nat.le_of_lt_succ h) (Nat.le_of_succ_le hk))
      · rw [← h]; exact e

theorem HasTy0.lift {Ψ Φ Γ X m} (e : HasTy0 S Ψ Φ Γ X (Tm.univ m)) :
    ∀ {k}, m ≤ k → k ≤ maxLevel → HasTy0 S Ψ Φ Γ X (Tm.univ k)
  | k, hmk, hk => by
    induction k with
    | zero => cases Nat.le_zero.1 hmk; exact e
    | succ k ih =>
      rcases Nat.lt_or_eq_of_le hmk with h | h
      · exact HasTy0.cumul hk (ih (Nat.le_of_lt_succ h) (Nat.le_of_succ_le hk))
      · rw [← h]; exact e

/-- `X ≡ T` at a universe of bounded level, or `X` equals a universe. -/
def Rel (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (X T : Tm) : Prop :=
  (∃ m, m ≤ maxLevel ∧ EqTm0 S Ψ Φ Γ X T (univ m)) ∨
    ∃ l m, m ≤ maxLevel ∧ EqTm0 S Ψ Φ Γ X (univ l) (univ m)

theorem Rel.refl {Ψ Φ Γ X l} (h : HasTy0 S Ψ Φ Γ X (univ l)) (hl : l ≤ maxLevel) : Rel S Ψ Φ Γ X X :=
  .inl ⟨l, hl, EqTm0.refl h⟩

theorem Rel.conv {Ψ Φ Γ X Y T k} : Rel S Ψ Φ Γ X Y → EqTm0 S Ψ Φ Γ Y T (univ k) → k ≤ maxLevel →
    Rel S Ψ Φ Γ X T
  | .inl ⟨m, hm, e⟩, e', hk => .inl ⟨max m k, Nat.max_le.2 ⟨hm, hk⟩,
      EqTm0.trans (e.lift (Nat.le_max_left _ _) (Nat.max_le.2 ⟨hm, hk⟩))
        (e'.lift (Nat.le_max_right _ _) (Nat.max_le.2 ⟨hm, hk⟩))⟩
  | .inr h, _, _ => .inr h

theorem Rel.restrict {Ψ Φ Φ' Γ X T} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) :
    Rel S Ψ Φ Γ X T → Rel S Ψ Φ' Γ X T
  | .inl ⟨m, hm, e⟩ => .inl ⟨m, hm, EqTm0.restrict hs he e⟩
  | .inr ⟨l, m, hm, e⟩ => .inr ⟨l, m, hm, EqTm0.restrict hs he e⟩

theorem Rel.up {Ψ Φ Γ X l l'} : Rel S Ψ Φ Γ X (univ l) → Rel S Ψ Φ Γ X (univ l')
  | .inl ⟨m, hm, e⟩ => .inr ⟨l, m, hm, e⟩
  | .inr h => .inr h

/-- The target type, typed at a bounded level or a bounded universe. -/
def TB (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (T : Tm) : Prop :=
  (∃ l, l ≤ maxLevel ∧ HasTy0 S Ψ Φ Γ T (univ l)) ∨ ∃ l, T = univ l ∧ l ≤ maxLevel

theorem TB.restrict {Ψ Φ Φ' Γ T} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) :
    TB S Ψ Φ Γ T → TB S Ψ Φ' Γ T
  | .inl ⟨l, hl, h⟩ => .inl ⟨l, hl, HasTy0.restrict hs he h⟩
  | .inr h => .inr h

/-- A chain from a type former `X` (not a universe) to a type `T` that is typed collapses to one
equation; through a universe it is explosive (`noConf`). -/
theorem Rel.collapse {Ψ Φ Γ X T l} (r : Rel S Ψ Φ Γ X T) (hX : HasTy0 S Ψ Φ Γ X (univ l))
    (hl : l ≤ maxLevel) (hc : X.headClash (univ 0) = true) (hT : TB S Ψ Φ Γ T)
    (hTu : ∀ k, T ≠ univ k) : ∃ m, m ≤ maxLevel ∧ EqTm0 S Ψ Φ Γ X T (univ m) := by
  rcases r with h | ⟨k, m, hm, e⟩
  · exact h
  · rcases hT with ⟨l', hl', hT⟩ | ⟨k', rfl, _⟩
    · have hle := Nat.max_le.2 ⟨hl, hl'⟩
      exact ⟨max l l', hle, EqTm0.noConf (X := X) (Y := univ k) hc e
        (hX.lift (Nat.le_max_left _ _) hle) (hT.lift (Nat.le_max_right _ _) hle)⟩
    · exact absurd rfl (hTu k')

/-! ## Introduction forms and their natural types -/

/-- Terms typed by an introduction rule at a type former. -/
def isIntro : Tm → Bool
  | .lam .. | .pair .. | .plam _ | .con .. | .hcomp .. => true
  | _ => false

/-- `s` is typed at its natural type `X` by its introduction rule, with that rule's premises. -/
def IntroTy (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) : Tm → Tm → Prop
  | .lam A t, X => ∃ B l, X = pi A B ∧ HasTy0 S Ψ Φ Γ (pi A B) (univ l) ∧ HasTy0 S Ψ Φ (A :: Γ) t B
  | .pair a b, X => ∃ A B l, X = sigma A B ∧ HasTy0 S Ψ Φ Γ (sigma A B) (univ l) ∧
      HasTy0 S Ψ Φ Γ a A ∧ HasTy0 S Ψ Φ Γ b (B.inst a)
  | .plam t, X => (∃ A a b l, X = path A a b ∧ HasTy0 S Ψ Φ Γ (path A a b) (univ l) ∧
      HasTy0 S (Ψ + 1) Φ.shift Γ.dshift t A ∧
      EqTm0 S Ψ Φ Γ (t.dinst .zero) a (A.dinst .zero) ∧ EqTm0 S Ψ Φ Γ (t.dinst .one) b (A.dinst .one)) ∨
      ∃ A l, X = ipi A ∧ HasTy0 S Ψ Φ Γ (ipi A) (univ l) ∧ HasTy0 S (Ψ + 1) Φ.shift Γ.dshift t A
  | .con d c ps args rs, X => X = data d ps ∧ ∃ D C, S[d]? = some (.data D) ∧ D.ctors[c]? = some C ∧
      ps = Tm.ofList ps.toList ∧ HasTy0 S Ψ Φ Γ (data d ps) (univ D.level) ∧
      HasTele0 S Ψ Φ Γ ps D.params [] ∧
      HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse ∧
      rs.length = C.dims ∧ ∀ r ∈ rs, r.Scoped Ψ
  | .hcomp A φ u a, X => X = A ∧ ∃ l, HasTy0 S Ψ Φ Γ A (univ l) ∧ φ.Scoped Ψ ∧
      HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u A.dshift ∧ HasTy0 S Ψ Φ Γ a A ∧
      EqTm0 S Ψ (cof Φ φ) Γ (u.dinst .zero) a A
  | _, _ => False

theorem IntroTy.restrict {Ψ Φ Φ' Γ s X} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) :
    IntroTy S Ψ Φ Γ s X → IntroTy S Ψ Φ' Γ s X := by
  have hs1 : Φ'.shift.Scoped (Ψ + 1) := scoped_shift hs
  have he1 : I.Entails Φ'.shift Φ.shift := ent_shift he
  intro h
  match s, h with
  | .lam A t, ⟨B, l, hX, hp, ht⟩ => exact ⟨B, l, hX, HasTy0.restrict hs he hp, HasTy0.restrict hs he ht⟩
  | .pair a b, ⟨A, B, l, hX, hp, ha, hb⟩ =>
    exact ⟨A, B, l, hX, HasTy0.restrict hs he hp, HasTy0.restrict hs he ha, HasTy0.restrict hs he hb⟩
  | .plam t, .inl ⟨A, a, b, l, hX, hp, ht, e0, e1⟩ =>
    exact .inl ⟨A, a, b, l, hX, HasTy0.restrict hs he hp, HasTy0.restrict hs1 he1 ht,
      EqTm0.restrict hs he e0, EqTm0.restrict hs he e1⟩
  | .plam t, .inr ⟨A, l, hX, hp, ht⟩ =>
    exact .inr ⟨A, l, hX, HasTy0.restrict hs he hp, HasTy0.restrict hs1 he1 ht⟩
  | .con d c ps args rs, ⟨hX, D, C, hD, hC, hps, hd, ht1, ht2, hr, hrs⟩ =>
    exact ⟨hX, D, C, hD, hC, hps, HasTy0.restrict hs he hd, HasTele0.restrict hs he ht1,
      HasTele0.restrict hs he ht2, hr, hrs⟩
  | .hcomp A φ u a, ⟨hX, l, hA, hφ, hu, ha, hside⟩ =>
    have hs2 : (cof Φ' φ).Scoped Ψ := ⟨hs, hφ⟩
    exact ⟨hX, l, HasTy0.restrict hs he hA, hφ,
      HasTy0.restrict (scoped_shift hs2) (ent_shift (ent_and_mono he (ent_refl _))) hu,
      HasTy0.restrict hs he ha, EqTm0.restrict hs2 (ent_and_mono he (ent_refl _)) hside⟩

/-- The premises of the eliminator's typing rule (`HasTy0.elim`), except the scrutinee's. -/
structure ElimPrem (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (d : Nat) (D : DataDecl) (ps P bs : Tm)
    (m : Nat) : Prop where
  hD : S[d]? = some (.data D)
  hps : ps = Tm.ofList ps.toList
  hdata : HasTy0 S Ψ Φ Γ (data d ps) (univ D.level)
  hpt : HasTele0 S Ψ Φ Γ ps D.params []
  hP : HasTy0 S Ψ Φ (data d ps :: Γ) P (univ m)
  hbs : bs = Tm.ofList bs.toList
  hlen : bs.toList.length = D.ctors.length
  hbr : ∀ (c : Nat) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
    HasTy0 S Ψ Φ Γ b (D.branchTy d c C ps P)
  hcoh : ∀ (c : Nat) (C : Ctor) (b : Tm) (k : Nat) (ψ : I) (e : Tm), D.ctors[c]? = some C →
    bs.toList[c]? = some b → C.bnd[k]? = some (ψ, e) →
    EqTm0 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
      (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps P)

theorem ElimPrem.restrict {Ψ Φ Φ' Γ d D ps P bs m} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ)
    (h : ElimPrem S Ψ Φ Γ d D ps P bs m) : ElimPrem S Ψ Φ' Γ d D ps P bs m where
  hD := h.hD
  hps := h.hps
  hdata := HasTy0.restrict hs he h.hdata
  hpt := HasTele0.restrict hs he h.hpt
  hP := HasTy0.restrict hs he h.hP
  hbs := h.hbs
  hlen := h.hlen
  hbr := fun c C b hc hb => HasTy0.restrict hs he (h.hbr c C b hc hb)
  hcoh := fun c C b k ψ e hc hb hk => by
    have e0 := h.hcoh c C b k ψ e hc hb hk
    have hψ := scoped_cof_right (scoped_of_eq e0)
    exact EqTm0.restrict ⟨scoped_ren hs (fun i hi => by omega), hψ⟩
      (ent_and_mono (ent_ren he _) (ent_refl _)) e0

end KubusCore.Meta
