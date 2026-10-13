import KubusCore.Meta.Structural

/-!
# Metatheory: inversion of type formers

Generation lemmas for type formers: a typing of `Π A B` (and of `Σ`, `PathP`, `(i : I) → A`,
Glue types) comes from the formation rule at some level `l`, followed by conversions, so the
type is connected to `U l` by a chain of judgmental equalities at universes (`TyChain`). Along
such a chain typings can be transported, so the spec's inversion rules (`piDom`, …, `glueFib`)
are admissible. No injectivity is needed, since inversion starts from a syntactic type former.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- `X` and `Y` are connected by judgmental equalities at universes. -/
inductive TyChain (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) : Tm → Tm → Prop
  | refl (X : Tm) : TyChain S Ψ Φ Γ X X
  | step {X Y Z : Tm} {m : Nat} : EqTm0 S Ψ Φ Γ X Y (univ m) → TyChain S Ψ Φ Γ Y Z →
      TyChain S Ψ Φ Γ X Z

theorem TyChain.transport {Ψ Φ Γ X Y} : TyChain S Ψ Φ Γ X Y → ∀ {t}, HasTy0 S Ψ Φ Γ t X → HasTy0 S Ψ Φ Γ t Y
  | .refl _, _, h => h
  | .step e ch, _, h => ch.transport (HasTy0.conv h e)

theorem TyChain.snoc {Ψ Φ Γ X Y Z m} : TyChain S Ψ Φ Γ X Y → EqTm0 S Ψ Φ Γ Y Z (univ m) →
    TyChain S Ψ Φ Γ X Z
  | .refl _, e => .step e (.refl _)
  | .step e' ch, e => .step e' (ch.snoc e)

theorem TyChain.restrict {Ψ Φ Φ' Γ X Y} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) :
    TyChain S Ψ Φ Γ X Y → TyChain S Ψ Φ' Γ X Y
  | .refl _ => .refl _
  | .step e ch => .step (EqTm0.restrict hs he e) (ch.restrict hs he)

theorem TyChain.wk' (hS : SigClosed S) {Ψ Φ Γ B l X Y} (hB : HasTy0 S Ψ Φ Γ B (univ l)) :
    TyChain S Ψ Φ Γ X Y → TyChain S Ψ Φ (B :: Γ) X.shift Y.shift
  | .refl _ => .refl _
  | .step e ch => .step (EqTm0.wk hS hB e) (ch.wk' hS hB)

theorem TyChain.dwk (hS : SigClosed S) {Ψ Φ Γ X Y} :
    TyChain S Ψ Φ Γ X Y → TyChain S (Ψ + 1) Φ.shift Γ.dshift X.dshift Y.dshift
  | .refl _ => .refl _
  | .step e ch => .step (EqTm0.dwk hS e) (ch.dwk hS)

theorem HasTele0.restrict {Ψ Φ Φ' Γ} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) :
    ∀ {ts Δ prev}, HasTele0 S Ψ Φ Γ ts Δ prev → HasTele0 S Ψ Φ' Γ ts Δ prev
  | _, _, _, .nil h => .nil (h.restrict hs he)
  | _, _, _, .cons h0 h1 => .cons (HasTy0.restrict hs he h0) (HasTele0.restrict hs he h1)

section
variable (hS : SigClosed S)
include hS

/-- Weakening a chain between universes (whose shifts are themselves). -/
theorem TyChain.wk {Ψ Φ Γ A l l' l''} (ch : TyChain S Ψ Φ Γ (univ l) (univ l''))
    (hA : HasTy0 S Ψ Φ Γ A (univ l')) : TyChain S Ψ Φ (A :: Γ) (univ l) (univ l'') :=
  ch.wk' hS hA

theorem gen_pi {Ψ Φ Γ t T} (h : HasTy0 S Ψ Φ Γ t T) {A B} (ht : t = .pi A B) :
    ∃ l, (HasTy0 S Ψ Φ Γ A (univ l) ∧ HasTy0 S Ψ Φ (A :: Γ) B (univ l)) ∧ TyChain S Ψ Φ Γ (univ l) T :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 h1 => by
    obtain ⟨l, a, ch⟩ := gen_pi h0 ht
    exact ⟨l, a, ch.snoc h1⟩
  | .restrict hs he h2 => by
    obtain ⟨l, ⟨a, b⟩, ch⟩ := gen_pi h2 ht
    exact ⟨l, ⟨HasTy0.restrict hs he a, HasTy0.restrict hs he b⟩, ch.restrict hs he⟩
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul h0 h1 => by
    obtain ⟨l, ⟨a, b⟩, ch⟩ := gen_pi h1 ht
    have a' := ch.transport a
    exact ⟨_, ⟨HasTy0.cumul h0 a', HasTy0.cumul h0 ((ch.wk hS a).transport b)⟩, .refl _⟩
  | .pi h0 h1 => by cases ht; exact ⟨_, ⟨h0, h1⟩, .refl _⟩
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
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

theorem gen_sigma {Ψ Φ Γ t T} (h : HasTy0 S Ψ Φ Γ t T) {A B} (ht : t = .sigma A B) :
    ∃ l, (HasTy0 S Ψ Φ Γ A (univ l) ∧ HasTy0 S Ψ Φ (A :: Γ) B (univ l)) ∧ TyChain S Ψ Φ Γ (univ l) T :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 h1 => by
    obtain ⟨l, a, ch⟩ := gen_sigma h0 ht
    exact ⟨l, a, ch.snoc h1⟩
  | .restrict hs he h2 => by
    obtain ⟨l, ⟨a, b⟩, ch⟩ := gen_sigma h2 ht
    exact ⟨l, ⟨HasTy0.restrict hs he a, HasTy0.restrict hs he b⟩, ch.restrict hs he⟩
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul h0 h1 => by
    obtain ⟨l, ⟨a, b⟩, ch⟩ := gen_sigma h1 ht
    have a' := ch.transport a
    exact ⟨_, ⟨HasTy0.cumul h0 a', HasTy0.cumul h0 ((ch.wk hS a).transport b)⟩, .refl _⟩
  | .pi _ _ => by cases ht
  | .lam _ _ => by cases ht
  | .app _ _ => by cases ht
  | .sigma h0 h1 => by cases ht; exact ⟨_, ⟨h0, h1⟩, .refl _⟩
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
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

theorem gen_path {Ψ Φ Γ t T} (h : HasTy0 S Ψ Φ Γ t T) {A a b} (ht : t = .path A a b) :
    ∃ l, (HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (univ l) ∧ HasTy0 S Ψ Φ Γ a (A.dinst .zero) ∧
      HasTy0 S Ψ Φ Γ b (A.dinst .one)) ∧ TyChain S Ψ Φ Γ (univ l) T :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 h1 => by
    obtain ⟨l, a, ch⟩ := gen_path h0 ht
    exact ⟨l, a, ch.snoc h1⟩
  | .restrict hs he h2 => by
    obtain ⟨l, ⟨x, y, z⟩, ch⟩ := gen_path h2 ht
    exact ⟨l, ⟨HasTy0.restrict (scoped_shift hs) (ent_shift he) x, HasTy0.restrict hs he y,
      HasTy0.restrict hs he z⟩, ch.restrict hs he⟩
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul h0 h1 => by
    obtain ⟨l, ⟨x, y, z⟩, ch⟩ := gen_path h1 ht
    exact ⟨_, ⟨HasTy0.cumul h0 ((ch.dwk hS).transport x), y, z⟩, .refl _⟩
  | .pi _ _ => by cases ht
  | .lam _ _ => by cases ht
  | .app _ _ => by cases ht
  | .sigma _ _ => by cases ht
  | .pair _ _ _ => by cases ht
  | .fst _ => by cases ht
  | .snd _ => by cases ht
  | .path h0 h1 h2 => by cases ht; exact ⟨_, ⟨h0, h1, h2⟩, .refl _⟩
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
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

theorem gen_ipi {Ψ Φ Γ t T} (h : HasTy0 S Ψ Φ Γ t T) {A} (ht : t = .ipi A) :
    ∃ l, HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (univ l) ∧ TyChain S Ψ Φ Γ (univ l) T :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 h1 => by
    obtain ⟨l, a, ch⟩ := gen_ipi h0 ht
    exact ⟨l, a, ch.snoc h1⟩
  | .restrict hs he h2 => by
    obtain ⟨l, x, ch⟩ := gen_ipi h2 ht
    exact ⟨l, HasTy0.restrict (scoped_shift hs) (ent_shift he) x, ch.restrict hs he⟩
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul h0 h1 => by
    obtain ⟨l, x, ch⟩ := gen_ipi h1 ht
    exact ⟨_, HasTy0.cumul h0 ((ch.dwk hS).transport x), .refl _⟩
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
  | .ipi _ h1 => by cases ht; exact ⟨_, h1, .refl _⟩
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
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

theorem gen_glue {Ψ Φ Γ t T} (h : HasTy0 S Ψ Φ Γ t T) {A φ T' e} (ht : t = .glue A φ T' e) :
    ∃ l, (HasTy0 S Ψ Φ Γ A (univ l) ∧ φ.Scoped Ψ ∧ HasTy0 S Ψ (cof Φ φ) Γ T' (univ l) ∧
      HasTy0 S Ψ (cof Φ φ) Γ e (equiv T' A)) ∧ TyChain S Ψ Φ Γ (univ l) T :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 h1 => by
    obtain ⟨l, a, ch⟩ := gen_glue h0 ht
    exact ⟨l, a, ch.snoc h1⟩
  | .restrict hs he h2 => by
    obtain ⟨l, ⟨x, hφ, y, z⟩, ch⟩ := gen_glue h2 ht
    have hs' : (cof _ _).Scoped _ := ⟨hs, hφ⟩
    exact ⟨l, ⟨HasTy0.restrict hs he x, hφ, HasTy0.restrict hs' (ent_and_mono he (ent_refl _)) y,
      HasTy0.restrict hs' (ent_and_mono he (ent_refl _)) z⟩, ch.restrict hs he⟩
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul h0 h1 => by
    obtain ⟨l, ⟨x, hφ, y, z⟩, ch⟩ := gen_glue h1 ht
    have hs' : (cof _ _).Scoped _ := ⟨scoped_of_ty h1, hφ⟩
    exact ⟨_, ⟨HasTy0.cumul h0 (ch.transport x), hφ,
      HasTy0.cumul h0 ((ch.restrict hs' (ent_and_left _ _)).transport y), z⟩, .refl _⟩
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
  | .glue h0 h1 h2 h3 => by cases ht; exact ⟨_, ⟨h0, h1, h2, h3⟩, .refl _⟩
  | .glueEl _ _ _ _ _ => by cases ht
  | .unglue _ _ _ _ => by cases ht
  | .data _ _ _ => by cases ht
  | .con _ _ _ _ _ _ _ _ => by cases ht
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

theorem gen_data_tele {Ψ Φ Γ t T} (h : HasTy0 S Ψ Φ Γ t T) {d ps} (ht : t = .data d ps) :
    ∃ D, S[d]? = some (.data D) ∧ HasTele0 S Ψ Φ Γ ps D.params [] :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 _ => gen_data_tele h0 ht
  | .restrict hs he h2 => by
    obtain ⟨D, hD, ht⟩ := gen_data_tele h2 ht
    exact ⟨D, hD, ht.restrict hs he⟩
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul _ h1 => gen_data_tele h1 ht
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
  | .data h0 _ h2 => by cases ht; exact ⟨_, h0, h2⟩
  | .con _ _ _ _ _ _ _ _ => by cases ht
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

end

/-! ## The spec's inversion rules -/

theorem HasTy0.piDom (hS : SigClosed S) {Ψ Φ Γ A B l} (h : HasTy0 S Ψ Φ Γ (Tm.pi A B) (Tm.univ l)) :
    HasTy0 S Ψ Φ Γ A (Tm.univ l) := by
  obtain ⟨l0, ⟨a, _⟩, ch⟩ := gen_pi hS h rfl
  exact ch.transport a

theorem HasTy0.piCod (hS : SigClosed S) {Ψ Φ Γ A B l} (h : HasTy0 S Ψ Φ Γ (Tm.pi A B) (Tm.univ l)) :
    HasTy0 S Ψ Φ (A :: Γ) B (Tm.univ l) := by
  obtain ⟨l0, ⟨a, b⟩, ch⟩ := gen_pi hS h rfl
  exact (ch.wk hS a).transport b

theorem HasTy0.sigmaDom (hS : SigClosed S) {Ψ Φ Γ A B l} (h : HasTy0 S Ψ Φ Γ (Tm.sigma A B) (Tm.univ l)) :
    HasTy0 S Ψ Φ Γ A (Tm.univ l) := by
  obtain ⟨l0, ⟨a, _⟩, ch⟩ := gen_sigma hS h rfl
  exact ch.transport a

theorem HasTy0.sigmaCod (hS : SigClosed S) {Ψ Φ Γ A B l} (h : HasTy0 S Ψ Φ Γ (Tm.sigma A B) (Tm.univ l)) :
    HasTy0 S Ψ Φ (A :: Γ) B (Tm.univ l) := by
  obtain ⟨l0, ⟨a, b⟩, ch⟩ := gen_sigma hS h rfl
  exact (ch.wk hS a).transport b

theorem HasTy0.pathLine (hS : SigClosed S) {Ψ Φ Γ A a b l} (h : HasTy0 S Ψ Φ Γ (Tm.path A a b) (Tm.univ l)) :
    HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (Tm.univ l) := by
  obtain ⟨l0, ⟨x, _, _⟩, ch⟩ := gen_path hS h rfl
  exact (ch.dwk hS).transport x

theorem HasTy0.pathLeft (hS : SigClosed S) {Ψ Φ Γ A a b l} (h : HasTy0 S Ψ Φ Γ (Tm.path A a b) (Tm.univ l)) :
    HasTy0 S Ψ Φ Γ a (A.dinst .zero) := (gen_path hS h rfl).choose_spec.1.2.1

theorem HasTy0.pathRight (hS : SigClosed S) {Ψ Φ Γ A a b l} (h : HasTy0 S Ψ Φ Γ (Tm.path A a b) (Tm.univ l)) :
    HasTy0 S Ψ Φ Γ b (A.dinst .one) := (gen_path hS h rfl).choose_spec.1.2.2

theorem HasTy0.ipiLine (hS : SigClosed S) {Ψ Φ Γ A l} (h : HasTy0 S Ψ Φ Γ (Tm.ipi A) (Tm.univ l)) :
    HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (Tm.univ l) := by
  obtain ⟨l0, x, ch⟩ := gen_ipi hS h rfl
  exact (ch.dwk hS).transport x

theorem HasTy0.glueFib (hS : SigClosed S) {Ψ Φ Γ A φ T e l} (h : HasTy0 S Ψ Φ Γ (Tm.glue A φ T e) (Tm.univ l)) :
    HasTy0 S Ψ (cof Φ φ) Γ T (Tm.univ l) := by
  obtain ⟨l0, ⟨_, hφ, y, _⟩, ch⟩ := gen_glue hS h rfl
  have hs : (cof Φ φ).Scoped Ψ := ⟨scoped_of_ty h, hφ⟩
  exact (ch.restrict hs (ent_and_left _ _)).transport y

end KubusCore.Meta
