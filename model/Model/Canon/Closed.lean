import Model.Canon.CSub

/-!
# Canonicity: typed terms are scoped

A term typed in `Ψ; Φ; Γ` has its term variables below `|Γ|` and its interval variables below
`Ψ`. Hence closed typed terms at stage `k` are fixed by the identity substitution, and their
weakening is the substitution `ISub.wk`.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

variable {S : Sig}

theorem lookup_lt : ∀ {Γ : Ctx} {x : ℕ} {A : Tm}, Γ.lookup x = some A → x < Γ.length
  | [], _, _, h => by simp [Ctx.lookup] at h
  | _ :: _, 0, _, _ => by simp
  | _ :: Γ, x + 1, A, h => by
    simp only [Ctx.lookup, Option.map_eq_some_iff] at h
    obtain ⟨B, hB, -⟩ := h
    have := lookup_lt hB; simp; omega

theorem closedB_ofList {n m : ℕ} : ∀ {L : List Tm}, (∀ t ∈ L, t.closedB n m = true) → (Tm.ofList L).closedB n m = true
  | [], _ => rfl
  | t :: L, h => by
    simp only [Tm.ofList, Tm.closedB, Bool.and_eq_true]
    exact ⟨h t (List.mem_cons_self ..), closedB_ofList fun t' ht' => h t' (List.mem_cons_of_mem _ ht')⟩

theorem scopedB_of {r : I} {m : ℕ} (h : r.Scoped m) : r.scopedB m = true := (I.scopedB_iff m r).2 h

mutual

theorem closed_ty {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → t.closedB Γ.length Ψ = true
  | @HasTy0.var _ Ψ Φ Γ x A h0 h1 => by simp [Tm.closedB, lookup_lt h1]
  | @HasTy0.conv _ Ψ Φ Γ t A B l h0 h1 => closed_ty h0
  | @HasTy0.restrict _ Ψ Φ Φ' Γ t A h0 h1 h2 => closed_ty h2
  | @HasTy0.const _ Ψ Φ Γ k t A h0 h1 => rfl
  | @HasTy0.univ _ Ψ Φ Γ l h0 h1 => rfl
  | @HasTy0.cumul _ Ψ Φ Γ A l h0 h1 => closed_ty h1
  | @HasTy0.pi _ Ψ Φ Γ A B l h0 h1 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨closed_ty h0, by simpa using closed_ty h1⟩
  | @HasTy0.lam _ Ψ Φ Γ A B t l h0 h1 => by
    have := closed_ty h0
    simp only [Tm.closedB, Bool.and_eq_true] at this ⊢; exact ⟨this.1, by simpa using closed_ty h1⟩
  | @HasTy0.app _ Ψ Φ Γ A B f a h0 h1 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨closed_ty h0, closed_ty h1⟩
  | @HasTy0.sigma _ Ψ Φ Γ A B l h0 h1 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨closed_ty h0, by simpa using closed_ty h1⟩
  | @HasTy0.pair _ Ψ Φ Γ A B a b l h0 h1 h2 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨closed_ty h1, closed_ty h2⟩
  | @HasTy0.fst _ Ψ Φ Γ A B p h0 => by simp only [Tm.closedB]; exact closed_ty h0
  | @HasTy0.snd _ Ψ Φ Γ A B p h0 => by simp only [Tm.closedB]; exact closed_ty h0
  | @HasTy0.path _ Ψ Φ Γ A a b l h0 h1 h2 => by
    simp only [Tm.closedB, Bool.and_eq_true]
    exact ⟨⟨by simpa [Ctx.dshift] using closed_ty h0, closed_ty h1⟩, closed_ty h2⟩
  | @HasTy0.plam _ Ψ Φ Γ A a b t l h0 h1 h2 h3 => by
    simp only [Tm.closedB]; simpa [Ctx.dshift] using closed_ty h1
  | @HasTy0.papp _ Ψ Φ Γ A a b p r h0 h1 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨closed_ty h0, scopedB_of h1⟩
  | @HasTy0.ipi _ Ψ Φ Γ A l h0 h1 => by
    simp only [Tm.closedB]; simpa [Ctx.dshift] using closed_ty h1
  | @HasTy0.ilam _ Ψ Φ Γ A t l h0 h1 => by
    simp only [Tm.closedB]; simpa [Ctx.dshift] using closed_ty h1
  | @HasTy0.iapp _ Ψ Φ Γ A p r h0 h1 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨closed_ty h0, scopedB_of h1⟩
  | @HasTy0.split _ Ψ Φ Γ A φ ψ t u l h0 h1 h2 h3 h4 h5 h6 => by
    simp only [Tm.closedB, Bool.and_eq_true]
    exact ⟨⟨⟨scopedB_of h0, closed_ty h4⟩, scopedB_of h1⟩, closed_ty h5⟩
  | @HasTy0.abort _ Ψ Φ Γ A l h0 h1 => rfl
  | @HasTy0.transp _ Ψ Φ Γ A φ a l h0 h1 h2 h3 => by
    simp only [Tm.closedB, Bool.and_eq_true]
    exact ⟨⟨by simpa [Ctx.dshift] using closed_ty h0, scopedB_of h1⟩, closed_ty h3⟩
  | @HasTy0.hcomp _ Ψ Φ Γ A φ u a l h0 h1 h2 h3 h4 => by
    simp only [Tm.closedB, Bool.and_eq_true]
    exact ⟨⟨⟨closed_ty h0, scopedB_of h1⟩, by simpa [Ctx.dshift] using closed_ty h2⟩, closed_ty h3⟩
  | @HasTy0.glue _ Ψ Φ Γ A φ T e l h0 h1 h2 h3 => by
    simp only [Tm.closedB, Bool.and_eq_true]
    exact ⟨⟨⟨closed_ty h0, scopedB_of h1⟩, closed_ty h2⟩, closed_ty h3⟩
  | @HasTy0.glueEl _ Ψ Φ Γ A φ T e t a l h0 h1 h2 h3 h4 => by
    have := closed_ty h0
    simp only [Tm.closedB, Bool.and_eq_true] at this ⊢
    exact ⟨⟨⟨this.1.1.2, closed_ty h1⟩, closed_ty h2⟩, closed_ty h3⟩
  | @HasTy0.unglue _ Ψ Φ Γ A φ T e g l h0 h1 h2 h3 => by
    have := closed_ty h0
    simp only [Tm.closedB, Bool.and_eq_true] at this ⊢
    exact ⟨⟨this.1.1.2, closed_ty h2⟩, closed_ty h3⟩
  | @HasTy0.data _ Ψ Φ Γ d D ps h0 h1 h2 => by simp only [Tm.closedB]; exact closed_tele h2
  | @HasTy0.con _ Ψ Φ Γ d D c C ps args rs h0 h1 h2 h3 h4 h5 h6 h7 => by
    simp only [Tm.closedB, Bool.and_eq_true, List.all_eq_true]
    exact ⟨⟨closed_tele h4, closed_tele h5⟩, fun r hr => scopedB_of (h7 r hr)⟩
  | @HasTy0.elim _ Ψ Φ Γ d D ps P bs t m h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
    simp only [Tm.closedB, Bool.and_eq_true]
    refine ⟨⟨⟨closed_tele h3, by simpa using closed_ty h4⟩, ?_⟩, closed_ty h9⟩
    rw [h5]
    refine closedB_ofList fun b hb => ?_
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hb
    obtain ⟨C, hC⟩ : ∃ C, D.ctors[c]? = some C :=
      ⟨D.ctors[c]'(by omega), List.getElem?_eq_getElem _⟩
    exact closed_ty (h7 c C _ hC (List.getElem?_eq_getElem hc))

theorem closed_tele {Ψ Φ Γ ts Δ prev} : HasTele0 S Ψ Φ Γ ts Δ prev → ts.closedB Γ.length Ψ = true
  | @HasTele0.nil _ Ψ Φ Γ prev h0 => rfl
  | @HasTele0.cons _ Ψ Φ Γ a as A Δ prev h0 h1 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨closed_ty h0, closed_tele h1⟩

end

theorem isub_id_of_closed {k : ℕ} {t : Tm} (h : t.closedB 0 k = true) : t.isub (ISub.id k) = t :=
  closed_subst_id h (fun x hx => absurd hx (Nat.not_lt_zero _)) (fun i hi => by simp [ISub.id, hi])

theorem isub_wk_of_closed {k : ℕ} {t : Tm} (h : t.closedB 0 k = true) : t.isub (ISub.wk k) = t.dshift := by
  rw [dshift_eq]
  exact closed_subst_eq t 0 k _ _ _ _ h (fun x hx => absurd hx (Nat.not_lt_zero _)) (fun i hi => by simp [ISub.wk, hi])

variable (hW : WfSig S)
include hW

theorem closed_of_ty {k : ℕ} {t A : Tm} (h : HasTy S k .one [] t A) : t.closedB 0 k = true :=
  closed_ty (spec_to_minimal hW h)

end Model.Canon
