import KubusCore.Meta.SubstData

/-!
# Metatheory: generation lemmas for the syntactic side conditions

Typing derivations of `data`, `con`, `elim` and `transp` terms determine the lengths of their
argument lists. (Only the typing rule of the term former, `conv`, `restrict` and `cumul` can
conclude such a typing.)
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem tele_length {Ψ Φ Γ} : ∀ {ts Δ prev}, HasTele0 S Ψ Φ Γ ts Δ prev → ts.toList.length = Δ.length
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ h => by simp [Tm.toList, tele_length h]

theorem eqtele_length {Ψ Φ Γ} : ∀ {ts ts' Δ prev}, EqTele0 S Ψ Φ Γ ts ts' Δ prev →
    ts.toList.length = Δ.length ∧ ts'.toList.length = Δ.length
  | _, _, _, _, .nil _ => ⟨rfl, rfl⟩
  | _, _, _, _, .cons _ h => by simp [Tm.toList, (eqtele_length h).1, (eqtele_length h).2]
  | _, _, _, _, .dataInj _ h1 h2 _ => ⟨tele_length h1, tele_length h2⟩

theorem argTys_length (C : Ctor) (d np : Nat) : (C.argTys d np).length = C.args.length := by
  simp [Ctor.argTys]

theorem gen_data {Ψ Φ Γ t T} (h : HasTy0 S Ψ Φ Γ t T) {d ps} (ht : t = .data d ps) :
    ∃ D, S[d]? = some (.data D) ∧ ps.toList.length = D.params.length :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 _ => gen_data h0 ht
  | .restrict _ _ h2 => gen_data h2 ht
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul _ h1 => gen_data h1 ht
  | .pi _ _ => by cases ht
  | .lam _ _ => by cases ht
  | .app _ _ => by cases ht
  | .sigma _ _ => by cases ht
  | .pair _ _ _ => by cases ht
  | .fst _ => by cases ht
  | .snd _ => by cases ht
  | .path _ _ _ => by cases ht
  | .plam _ _ _ _ => by cases ht
  | .papp _ _ => by cases ht
  | .ipi _ _ => by cases ht
  | .ilam _ _ => by cases ht
  | .iapp _ _ => by cases ht
  | .split _ _ _ _ _ _ _ => by cases ht
  | .abort _ _ => by cases ht
  | .transp _ _ _ _ => by cases ht
  | .hcomp _ _ _ _ _ => by cases ht
  | .glue _ _ _ _ => by cases ht
  | .glueEl _ _ _ _ _ => by cases ht
  | .unglue _ _ _ _ => by cases ht
  | .data h0 _ h2 => by cases ht; exact ⟨_, h0, tele_length h2⟩
  | .con _ _ _ _ _ _ _ _ => by cases ht
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

theorem gen_con {Ψ Φ Γ t T} (h : HasTy0 S Ψ Φ Γ t T) {d c ps args rs}
    (ht : t = .con d c ps args rs) :
    ∃ D C, S[d]? = some (.data D) ∧ D.ctors[c]? = some C ∧ IsList ps ∧
      ps.toList.length = D.params.length ∧ args.toList.length = C.args.length ∧ rs.length = C.dims :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 _ => gen_con h0 ht
  | .restrict _ _ h2 => gen_con h2 ht
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul _ h1 => gen_con h1 ht
  | .pi _ _ => by cases ht
  | .lam _ _ => by cases ht
  | .app _ _ => by cases ht
  | .sigma _ _ => by cases ht
  | .pair _ _ _ => by cases ht
  | .fst _ => by cases ht
  | .snd _ => by cases ht
  | .path _ _ _ => by cases ht
  | .plam _ _ _ _ => by cases ht
  | .papp _ _ => by cases ht
  | .ipi _ _ => by cases ht
  | .ilam _ _ => by cases ht
  | .iapp _ _ => by cases ht
  | .split _ _ _ _ _ _ _ => by cases ht
  | .abort _ _ => by cases ht
  | .transp _ _ _ _ => by cases ht
  | .hcomp _ _ _ _ _ => by cases ht
  | .glue _ _ _ _ => by cases ht
  | .glueEl _ _ _ _ _ => by cases ht
  | .unglue _ _ _ _ => by cases ht
  | .data _ _ _ => by cases ht
  | .con h0 h1 h2 _ h4 h5 h6 _ => by
    cases ht
    exact ⟨_, _, h0, h1, h2, tele_length h4, by rw [tele_length h5, argTys_length], h6⟩
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

theorem gen_elim {Ψ Φ Γ t T} (h : HasTy0 S Ψ Φ Γ t T) {d ps P bs u}
    (ht : t = .elim d ps P bs u) :
    ∃ D, S[d]? = some (.data D) ∧ IsList ps ∧ ps.toList.length = D.params.length ∧ IsList bs :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 _ => gen_elim h0 ht
  | .restrict _ _ h2 => gen_elim h2 ht
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul _ h1 => gen_elim h1 ht
  | .pi _ _ => by cases ht
  | .lam _ _ => by cases ht
  | .app _ _ => by cases ht
  | .sigma _ _ => by cases ht
  | .pair _ _ _ => by cases ht
  | .fst _ => by cases ht
  | .snd _ => by cases ht
  | .path _ _ _ => by cases ht
  | .plam _ _ _ _ => by cases ht
  | .papp _ _ => by cases ht
  | .ipi _ _ => by cases ht
  | .ilam _ _ => by cases ht
  | .iapp _ _ => by cases ht
  | .split _ _ _ _ _ _ _ => by cases ht
  | .abort _ _ => by cases ht
  | .transp _ _ _ _ => by cases ht
  | .hcomp _ _ _ _ _ => by cases ht
  | .glue _ _ _ _ => by cases ht
  | .glueEl _ _ _ _ _ => by cases ht
  | .unglue _ _ _ _ => by cases ht
  | .data _ _ _ => by cases ht
  | .con _ _ _ _ _ _ _ _ => by cases ht
  | .elim h0 h1 _ h3 _ h5 _ _ _ _ => by
    cases ht
    exact ⟨_, h0, h1, tele_length h3, h5⟩

/-- The line of a transport is a type (under a weaker restriction). -/
theorem gen_transp {Ψ Φ Γ t T} (h : HasTy0 S Ψ Φ Γ t T) {A φ a} (ht : t = .transp A φ a) :
    ∃ Φ0 l, I.Entails Φ Φ0 ∧ HasTy0 S (Ψ + 1) Φ0.shift Γ.dshift A (univ l) :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 _ => gen_transp h0 ht
  | .restrict _ h1 h2 => by
    obtain ⟨Φ0, l, he, h⟩ := gen_transp h2 ht
    exact ⟨Φ0, l, ent_trans h1 he, h⟩
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul _ h1 => gen_transp h1 ht
  | .pi _ _ => by cases ht
  | .lam _ _ => by cases ht
  | .app _ _ => by cases ht
  | .sigma _ _ => by cases ht
  | .pair _ _ _ => by cases ht
  | .fst _ => by cases ht
  | .snd _ => by cases ht
  | .path _ _ _ => by cases ht
  | .plam _ _ _ _ => by cases ht
  | .papp _ _ => by cases ht
  | .ipi _ _ => by cases ht
  | .ilam _ _ => by cases ht
  | .iapp _ _ => by cases ht
  | .split _ _ _ _ _ _ _ => by cases ht
  | .abort _ _ => by cases ht
  | .transp h0 _ _ _ => by cases ht; exact ⟨_, _, ent_refl _, h0⟩
  | .hcomp _ _ _ _ _ => by cases ht
  | .glue _ _ _ _ => by cases ht
  | .glueEl _ _ _ _ _ => by cases ht
  | .unglue _ _ _ _ => by cases ht
  | .data _ _ _ => by cases ht
  | .con _ _ _ _ _ _ _ _ => by cases ht
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

theorem gen_transp_data {Ψ Φ Γ t T} (h : HasTy0 S Ψ Φ Γ t T) {d ps φ a}
    (ht : t = .transp (.data d ps) φ a) :
    ∃ D, S[d]? = some (.data D) ∧ ps.toList.length = D.params.length := by
  obtain ⟨_, _, _, h⟩ := gen_transp h ht
  exact gen_data h rfl

theorem dinst_toList {ps : Tm} (h : IsList ps) (r : I) :
    (ps.dinst r).toList = ps.toList.map (·.dinst r) := toList_subst h _ _

theorem dataInjAt_ty_subst {ps A : Tm} {k : Nat} (h : IsList ps) (hA : A.closedB k 0 = true)
    (hk : k < ps.toList.length) (σ : Nat → Tm) (τ : Nat → I) :
    (A.substList (ps.toList.take k).reverse).subst σ τ = A.substList ((ps.subst σ τ).toList.take k).reverse := by
  have hl : ((ps.toList.take k).reverse).length = k := by simp [List.length_take]; omega
  rw [substList_subst (by rw [hl]; exact hA), toList_subst h, ← List.map_take, List.map_reverse]

end KubusCore.Meta
