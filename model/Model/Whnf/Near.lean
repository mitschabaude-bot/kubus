import Model.Whnf.Step

/-!
# Terms equal up to `I.Eq` at their interval positions

`TmNear t t'`: `t` and `t'` have the same shape, and their interval subterms are equal as elements
of the De Morgan algebra (`I.Eq`). Restrictions by pointwise `I.Eq`-equal interval substitutions give
near terms, and weak-head reduction respects nearness (`step_near`): face decisions agree, and the
contracta are built by congruent operations.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta

/-- Faces equal up to mutual entailment. -/
def FEq (φ φ' : I) : Prop := I.Entails φ φ' ∧ I.Entails φ' φ

theorem FEq.refl (φ : I) : FEq φ φ := ⟨ent_refl _, ent_refl _⟩
theorem FEq.symm {φ φ' : I} (h : FEq φ φ') : FEq φ' φ := ⟨h.2, h.1⟩
theorem FEq.trans {φ φ' φ'' : I} (h : FEq φ φ') (h' : FEq φ' φ'') : FEq φ φ'' :=
  ⟨ent_trans h.1 h'.1, ent_trans h'.2 h.2⟩
theorem FEq.of_eq {φ φ' : I} (h : I.Eq φ φ') : FEq φ φ' := ⟨eq_ent h, eq_ent (I_eq_symm h)⟩
theorem FEq.subst2 {φ φ' : I} (h : FEq φ φ') {τ τ' : ℕ → I} (hτ : ∀ i, I.Eq (τ i) (τ' i)) :
    FEq (φ.subst τ) (φ'.subst τ') :=
  ⟨ent_trans (ent_subst h.1 τ) (eq_ent (I_eq_subst_congr hτ φ')),
    ent_trans (eq_ent (I_eq_subst_congr (fun i => I_eq_symm (hτ i)) φ')) (ent_subst h.2 τ)⟩
theorem FEq.ren {φ φ' : I} (h : FEq φ φ') (δ : ℕ → ℕ) : FEq (φ.ren δ) (φ'.ren δ) :=
  ⟨ent_subst h.1 _, ent_subst h.2 _⟩

/-- Terms equal up to `I.Eq` at their interval points, and up to mutual entailment at their faces. -/
inductive TmNear : Tm → Tm → Prop
  | var (x : ℕ) : TmNear (.var x) (.var x)
  | const (c : ℕ) : TmNear (.const c) (.const c)
  | univ (l : ℕ) : TmNear (.univ l) (.univ l)
  | pi {A A' B B' : Tm} : TmNear A A' → TmNear B B' → TmNear (.pi A B) (.pi A' B')
  | lam {A A' t t' : Tm} : TmNear A A' → TmNear t t' → TmNear (.lam A t) (.lam A' t')
  | app {f f' a a' : Tm} : TmNear f f' → TmNear a a' → TmNear (.app f a) (.app f' a')
  | sigma {A A' B B' : Tm} : TmNear A A' → TmNear B B' → TmNear (.sigma A B) (.sigma A' B')
  | pair {a a' b b' : Tm} : TmNear a a' → TmNear b b' → TmNear (.pair a b) (.pair a' b')
  | fst {p p' : Tm} : TmNear p p' → TmNear (.fst p) (.fst p')
  | snd {p p' : Tm} : TmNear p p' → TmNear (.snd p) (.snd p')
  | path {A A' a a' b b' : Tm} : TmNear A A' → TmNear a a' → TmNear b b' →
      TmNear (.path A a b) (.path A' a' b')
  | plam {t t' : Tm} : TmNear t t' → TmNear (.plam t) (.plam t')
  | papp {p p' : Tm} {r r' : I} : TmNear p p' → I.Eq r r' → TmNear (.papp p r) (.papp p' r')
  | ipi {A A' : Tm} : TmNear A A' → TmNear (.ipi A) (.ipi A')
  | split {φ φ' ψ ψ' : I} {t t' u u' : Tm} : FEq φ φ' → TmNear t t' → FEq ψ ψ' → TmNear u u' →
      TmNear (.split φ t ψ u) (.split φ' t' ψ' u')
  | abort : TmNear .abort .abort
  | transp {A A' a a' : Tm} {φ φ' : I} : TmNear A A' → FEq φ φ' → TmNear a a' →
      TmNear (.transp A φ a) (.transp A' φ' a')
  | hcomp {A A' u u' a a' : Tm} {φ φ' : I} : TmNear A A' → FEq φ φ' → TmNear u u' → TmNear a a' →
      TmNear (.hcomp A φ u a) (.hcomp A' φ' u' a')
  | glue {A A' T T' e e' : Tm} {φ φ' : I} : TmNear A A' → FEq φ φ' → TmNear T T' → TmNear e e' →
      TmNear (.glue A φ T e) (.glue A' φ' T' e')
  | glueEl {e e' t t' a a' : Tm} {φ φ' : I} : FEq φ φ' → TmNear e e' → TmNear t t' → TmNear a a' →
      TmNear (.glueEl φ e t a) (.glueEl φ' e' t' a')
  | unglue {e e' g g' : Tm} {φ φ' : I} : FEq φ φ' → TmNear e e' → TmNear g g' →
      TmNear (.unglue φ e g) (.unglue φ' e' g')
  | tnil : TmNear .tnil .tnil
  | tcons {t t' ts ts' : Tm} : TmNear t t' → TmNear ts ts' → TmNear (.tcons t ts) (.tcons t' ts')
  | data {d : ℕ} {ps ps' : Tm} : TmNear ps ps' → TmNear (.data d ps) (.data d ps')
  | con {d c : ℕ} {ps ps' args args' : Tm} {rs rs' : List I} : TmNear ps ps' → TmNear args args' →
      List.Forall₂ I.Eq rs rs' → TmNear (.con d c ps args rs) (.con d c ps' args' rs')
  | elim {d : ℕ} {ps ps' P P' bs bs' t t' : Tm} : TmNear ps ps' → TmNear P P' → TmNear bs bs' →
      TmNear t t' → TmNear (.elim d ps P bs t) (.elim d ps' P' bs' t')

namespace TmNear

theorem forall2_refl : ∀ (rs : List I), List.Forall₂ I.Eq rs rs
  | [] => .nil
  | r :: rs => .cons (I_eq_refl r) (forall2_refl rs)

theorem refl : ∀ (t : Tm), TmNear t t
  | .var x => .var x
  | .const c => .const c
  | .univ l => .univ l
  | .pi A B => .pi (refl A) (refl B)
  | .lam A t => .lam (refl A) (refl t)
  | .app f a => .app (refl f) (refl a)
  | .sigma A B => .sigma (refl A) (refl B)
  | .pair a b => .pair (refl a) (refl b)
  | .fst p => .fst (refl p)
  | .snd p => .snd (refl p)
  | .path A a b => .path (refl A) (refl a) (refl b)
  | .plam t => .plam (refl t)
  | .papp p r => .papp (refl p) (I_eq_refl r)
  | .ipi A => .ipi (refl A)
  | .split φ t ψ u => .split (FEq.refl φ) (refl t) (FEq.refl ψ) (refl u)
  | .abort => .abort
  | .transp A φ a => .transp (refl A) (FEq.refl φ) (refl a)
  | .hcomp A φ u a => .hcomp (refl A) (FEq.refl φ) (refl u) (refl a)
  | .glue A φ T e => .glue (refl A) (FEq.refl φ) (refl T) (refl e)
  | .glueEl φ e t a => .glueEl (FEq.refl φ) (refl e) (refl t) (refl a)
  | .unglue φ e g => .unglue (FEq.refl φ) (refl e) (refl g)
  | .tnil => .tnil
  | .tcons t ts => .tcons (refl t) (refl ts)
  | .data _ ps => .data (refl ps)
  | .con _ _ ps args rs => .con (refl ps) (refl args) (forall2_refl rs)
  | .elim _ ps P bs t => .elim (refl ps) (refl P) (refl bs) (refl t)

theorem symm {t t' : Tm} (h : TmNear t t') : TmNear t' t := by
  induction h with
  | var => exact .var _
  | const => exact .const _
  | univ => exact .univ _
  | pi _ _ ih1 ih2 => exact .pi ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | sigma _ _ ih1 ih2 => exact .sigma ih1 ih2
  | pair _ _ ih1 ih2 => exact .pair ih1 ih2
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | path _ _ _ ih1 ih2 ih3 => exact .path ih1 ih2 ih3
  | plam _ ih => exact .plam ih
  | papp _ e ih => exact .papp ih (I_eq_symm e)
  | ipi _ ih => exact .ipi ih
  | split e1 _ e2 _ ih1 ih2 => exact .split e1.symm ih1 e2.symm ih2
  | abort => exact .abort
  | transp _ e _ ih1 ih2 => exact .transp ih1 e.symm ih2
  | hcomp _ e _ _ ih1 ih2 ih3 => exact .hcomp ih1 e.symm ih2 ih3
  | glue _ e _ _ ih1 ih2 ih3 => exact .glue ih1 e.symm ih2 ih3
  | glueEl e _ _ _ ih1 ih2 ih3 => exact .glueEl e.symm ih1 ih2 ih3
  | unglue e _ _ ih1 ih2 => exact .unglue e.symm ih1 ih2
  | tnil => exact .tnil
  | tcons _ _ ih1 ih2 => exact .tcons ih1 ih2
  | data _ ih => exact .data ih
  | con _ _ hrs ih1 ih2 => exact .con ih1 ih2 (hrs.flip.imp fun _ _ e => I_eq_symm e)
  | elim _ _ _ _ ih1 ih2 ih3 ih4 => exact .elim ih1 ih2 ih3 ih4

theorem forall2_trans : ∀ {rs rs' rs'' : List I}, List.Forall₂ I.Eq rs rs' → List.Forall₂ I.Eq rs' rs'' →
    List.Forall₂ I.Eq rs rs''
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons e h, .cons e' h' => .cons (I_eq_trans e e') (forall2_trans h h')

theorem forall2_map {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') (f g : I → I)
    (hf : ∀ r r', I.Eq r r' → I.Eq (f r) (g r')) : List.Forall₂ I.Eq (rs.map f) (rs'.map g) := by
  induction h with
  | nil => exact .nil
  | cons e _ ih => exact .cons (hf _ _ e) ih

theorem trans {t t' t'' : Tm} (h : TmNear t t') (h' : TmNear t' t'') : TmNear t t'' := by
  induction h generalizing t'' with
  | var => exact h'
  | const => exact h'
  | univ => exact h'
  | pi _ _ ih1 ih2 => cases h' with | pi a b => exact .pi (ih1 a) (ih2 b)
  | lam _ _ ih1 ih2 => cases h' with | lam a b => exact .lam (ih1 a) (ih2 b)
  | app _ _ ih1 ih2 => cases h' with | app a b => exact .app (ih1 a) (ih2 b)
  | sigma _ _ ih1 ih2 => cases h' with | sigma a b => exact .sigma (ih1 a) (ih2 b)
  | pair _ _ ih1 ih2 => cases h' with | pair a b => exact .pair (ih1 a) (ih2 b)
  | fst _ ih => cases h' with | fst a => exact .fst (ih a)
  | snd _ ih => cases h' with | snd a => exact .snd (ih a)
  | path _ _ _ ih1 ih2 ih3 => cases h' with | path a b c => exact .path (ih1 a) (ih2 b) (ih3 c)
  | plam _ ih => cases h' with | plam a => exact .plam (ih a)
  | papp _ e ih => cases h' with | papp a e' => exact .papp (ih a) (I_eq_trans e e')
  | ipi _ ih => cases h' with | ipi a => exact .ipi (ih a)
  | split e1 _ e2 _ ih1 ih2 => cases h' with
    | split f1 a f2 b => exact .split (e1.trans f1) (ih1 a) (e2.trans f2) (ih2 b)
  | abort => exact h'
  | transp _ e _ ih1 ih2 => cases h' with | transp a f b => exact .transp (ih1 a) (e.trans f) (ih2 b)
  | hcomp _ e _ _ ih1 ih2 ih3 => cases h' with
    | hcomp a f b c => exact .hcomp (ih1 a) (e.trans f) (ih2 b) (ih3 c)
  | glue _ e _ _ ih1 ih2 ih3 => cases h' with
    | glue a f b c => exact .glue (ih1 a) (e.trans f) (ih2 b) (ih3 c)
  | glueEl e _ _ _ ih1 ih2 ih3 => cases h' with
    | glueEl f a b c => exact .glueEl (e.trans f) (ih1 a) (ih2 b) (ih3 c)
  | unglue e _ _ ih1 ih2 => cases h' with | unglue f a b => exact .unglue (e.trans f) (ih1 a) (ih2 b)
  | tnil => exact h'
  | tcons _ _ ih1 ih2 => cases h' with | tcons a b => exact .tcons (ih1 a) (ih2 b)
  | data _ ih => cases h' with | data a => exact .data (ih a)
  | con _ _ hrs ih1 ih2 => cases h' with
    | con a b hrs' => exact .con (ih1 a) (ih2 b) (forall2_trans hrs hrs')
  | elim _ _ _ _ ih1 ih2 ih3 ih4 => cases h' with
    | elim a b c d => exact .elim (ih1 a) (ih2 b) (ih3 c) (ih4 d)

theorem ieq_subst2 {r r' : I} (h : I.Eq r r') {τ τ' : ℕ → I} (hτ : ∀ i, I.Eq (τ i) (τ' i)) :
    I.Eq (r.subst τ) (r'.subst τ') :=
  I_eq_trans (I_eq_subst h τ) (I_eq_subst_congr hτ r')

theorem ren {t t' : Tm} (h : TmNear t t') : ∀ (ρ δ : ℕ → ℕ), TmNear (t.ren ρ δ) (t'.ren ρ δ) := by
  have ie : ∀ {r r' : I}, I.Eq r r' → ∀ δ : ℕ → ℕ, I.Eq (r.ren δ) (r'.ren δ) := fun e δ => I_eq_subst e _
  induction h with
  | var => intro ρ δ; exact refl _
  | const => intro ρ δ; exact refl _
  | univ => intro ρ δ; exact refl _
  | pi _ _ ih1 ih2 => intro ρ δ; exact .pi (ih1 ρ δ) (ih2 _ δ)
  | lam _ _ ih1 ih2 => intro ρ δ; exact .lam (ih1 ρ δ) (ih2 _ δ)
  | app _ _ ih1 ih2 => intro ρ δ; exact .app (ih1 ρ δ) (ih2 ρ δ)
  | sigma _ _ ih1 ih2 => intro ρ δ; exact .sigma (ih1 ρ δ) (ih2 _ δ)
  | pair _ _ ih1 ih2 => intro ρ δ; exact .pair (ih1 ρ δ) (ih2 ρ δ)
  | fst _ ih => intro ρ δ; exact .fst (ih ρ δ)
  | snd _ ih => intro ρ δ; exact .snd (ih ρ δ)
  | path _ _ _ ih1 ih2 ih3 => intro ρ δ; exact .path (ih1 ρ _) (ih2 ρ δ) (ih3 ρ δ)
  | plam _ ih => intro ρ δ; exact .plam (ih ρ _)
  | papp _ e ih => intro ρ δ; exact .papp (ih ρ δ) (ie e δ)
  | ipi _ ih => intro ρ δ; exact .ipi (ih ρ _)
  | split e1 _ e2 _ ih1 ih2 => intro ρ δ; exact .split (e1.ren δ) (ih1 ρ δ) (e2.ren δ) (ih2 ρ δ)
  | abort => intro ρ δ; exact .abort
  | transp _ e _ ih1 ih2 => intro ρ δ; exact .transp (ih1 ρ _) (e.ren δ) (ih2 ρ δ)
  | hcomp _ e _ _ ih1 ih2 ih3 => intro ρ δ; exact .hcomp (ih1 ρ δ) (e.ren δ) (ih2 ρ _) (ih3 ρ δ)
  | glue _ e _ _ ih1 ih2 ih3 => intro ρ δ; exact .glue (ih1 ρ δ) (e.ren δ) (ih2 ρ δ) (ih3 ρ δ)
  | glueEl e _ _ _ ih1 ih2 ih3 => intro ρ δ; exact .glueEl (e.ren δ) (ih1 ρ δ) (ih2 ρ δ) (ih3 ρ δ)
  | unglue e _ _ ih1 ih2 => intro ρ δ; exact .unglue (e.ren δ) (ih1 ρ δ) (ih2 ρ δ)
  | tnil => intro ρ δ; exact .tnil
  | tcons _ _ ih1 ih2 => intro ρ δ; exact .tcons (ih1 ρ δ) (ih2 ρ δ)
  | data _ ih => intro ρ δ; exact .data (ih ρ δ)
  | con _ _ hrs ih1 ih2 => intro ρ δ; exact .con (ih1 ρ δ) (ih2 ρ δ) (forall2_map hrs _ _ fun _ _ e => ie e δ)
  | elim _ _ _ _ ih1 ih2 ih3 ih4 => intro ρ δ; exact .elim (ih1 ρ δ) (ih2 _ δ) (ih3 ρ δ) (ih4 ρ δ)

theorem shift {t t' : Tm} (h : TmNear t t') : TmNear t.shift t'.shift := h.ren _ _
theorem dshift {t t' : Tm} (h : TmNear t t') : TmNear t.dshift t'.dshift := h.ren _ _

theorem subst {t t' : Tm} (h : TmNear t t') :
    ∀ {σ σ' : ℕ → Tm} {τ τ' : ℕ → I}, (∀ n, TmNear (σ n) (σ' n)) → (∀ i, I.Eq (τ i) (τ' i)) →
      TmNear (t.subst σ τ) (t'.subst σ' τ') := by
  have upσ : ∀ {σ σ' : ℕ → Tm}, (∀ n, TmNear (σ n) (σ' n)) → ∀ n, TmNear (Tm.up σ n) (Tm.up σ' n) := by
    intro σ σ' hσ n; rcases n with _ | n
    · exact refl _
    · exact (hσ n).shift
  have dσ : ∀ {σ σ' : ℕ → Tm}, (∀ n, TmNear (σ n) (σ' n)) → ∀ n, TmNear ((σ n).dshift) ((σ' n).dshift) :=
    fun hσ n => (hσ n).dshift
  have upτ : ∀ {τ τ' : ℕ → I}, (∀ i, I.Eq (τ i) (τ' i)) → ∀ i, I.Eq (I.up τ i) (I.up τ' i) := by
    intro τ τ' hτ i; rcases i with _ | i
    · exact I_eq_refl _
    · exact I_eq_subst (hτ i) _
  induction h with
  | var => intro σ σ' τ τ' hσ hτ; exact hσ _
  | const => intro σ σ' τ τ' hσ hτ; exact refl _
  | univ => intro σ σ' τ τ' hσ hτ; exact refl _
  | pi _ _ ih1 ih2 => intro σ σ' τ τ' hσ hτ; exact .pi (ih1 hσ hτ) (ih2 (upσ hσ) hτ)
  | lam _ _ ih1 ih2 => intro σ σ' τ τ' hσ hτ; exact .lam (ih1 hσ hτ) (ih2 (upσ hσ) hτ)
  | app _ _ ih1 ih2 => intro σ σ' τ τ' hσ hτ; exact .app (ih1 hσ hτ) (ih2 hσ hτ)
  | sigma _ _ ih1 ih2 => intro σ σ' τ τ' hσ hτ; exact .sigma (ih1 hσ hτ) (ih2 (upσ hσ) hτ)
  | pair _ _ ih1 ih2 => intro σ σ' τ τ' hσ hτ; exact .pair (ih1 hσ hτ) (ih2 hσ hτ)
  | fst _ ih => intro σ σ' τ τ' hσ hτ; exact .fst (ih hσ hτ)
  | snd _ ih => intro σ σ' τ τ' hσ hτ; exact .snd (ih hσ hτ)
  | path _ _ _ ih1 ih2 ih3 => intro σ σ' τ τ' hσ hτ; exact .path (ih1 (dσ hσ) (upτ hτ)) (ih2 hσ hτ) (ih3 hσ hτ)
  | plam _ ih => intro σ σ' τ τ' hσ hτ; exact .plam (ih (dσ hσ) (upτ hτ))
  | papp _ e ih => intro σ σ' τ τ' hσ hτ; exact .papp (ih hσ hτ) (ieq_subst2 e hτ)
  | ipi _ ih => intro σ σ' τ τ' hσ hτ; exact .ipi (ih (dσ hσ) (upτ hτ))
  | split e1 _ e2 _ ih1 ih2 =>
    intro σ σ' τ τ' hσ hτ
    exact .split (e1.subst2 hτ) (ih1 hσ hτ) (e2.subst2 hτ) (ih2 hσ hτ)
  | abort => intro σ σ' τ τ' hσ hτ; exact .abort
  | transp _ e _ ih1 ih2 =>
    intro σ σ' τ τ' hσ hτ
    exact .transp (ih1 (dσ hσ) (upτ hτ)) (e.subst2 hτ) (ih2 hσ hτ)
  | hcomp _ e _ _ ih1 ih2 ih3 =>
    intro σ σ' τ τ' hσ hτ
    exact .hcomp (ih1 hσ hτ) (e.subst2 hτ) (ih2 (dσ hσ) (upτ hτ)) (ih3 hσ hτ)
  | glue _ e _ _ ih1 ih2 ih3 =>
    intro σ σ' τ τ' hσ hτ
    exact .glue (ih1 hσ hτ) (e.subst2 hτ) (ih2 hσ hτ) (ih3 hσ hτ)
  | glueEl e _ _ _ ih1 ih2 ih3 =>
    intro σ σ' τ τ' hσ hτ
    exact .glueEl (e.subst2 hτ) (ih1 hσ hτ) (ih2 hσ hτ) (ih3 hσ hτ)
  | unglue e _ _ ih1 ih2 => intro σ σ' τ τ' hσ hτ; exact .unglue (e.subst2 hτ) (ih1 hσ hτ) (ih2 hσ hτ)
  | tnil => intro σ σ' τ τ' hσ hτ; exact .tnil
  | tcons _ _ ih1 ih2 => intro σ σ' τ τ' hσ hτ; exact .tcons (ih1 hσ hτ) (ih2 hσ hτ)
  | data _ ih => intro σ σ' τ τ' hσ hτ; exact .data (ih hσ hτ)
  | con _ _ hrs ih1 ih2 =>
    intro σ σ' τ τ' hσ hτ
    exact .con (ih1 hσ hτ) (ih2 hσ hτ) (forall2_map hrs _ _ fun _ _ e => ieq_subst2 e hτ)
  | elim _ _ _ _ ih1 ih2 ih3 ih4 =>
    intro σ σ' τ τ' hσ hτ
    exact .elim (ih1 hσ hτ) (ih2 (upσ hσ) hτ) (ih3 hσ hτ) (ih4 hσ hτ)

theorem dsubst {t t' : Tm} (h : TmNear t t') {τ τ' : ℕ → I} (hτ : ∀ i, I.Eq (τ i) (τ' i)) :
    TmNear (t.dsubst τ) (t'.dsubst τ') := h.subst (fun n => refl _) hτ

theorem dinst {t t' : Tm} (h : TmNear t t') {r r' : I} (hr : I.Eq r r') : TmNear (t.dinst r) (t'.dinst r') :=
  h.dsubst fun i => by rcases i with _ | i
                       · exact hr
                       · exact I_eq_refl _

theorem inst {t t' a a' : Tm} (h : TmNear t t') (ha : TmNear a a') : TmNear (t.inst a) (t'.inst a') :=
  h.subst (fun n => by rcases n with _ | n
                       · exact ha
                       · exact refl _) fun i => I_eq_refl _

end TmNear

theorem FEq.entails {φ φ' : I} (h : FEq φ φ') : I.entails .one φ = I.entails .one φ' := by
  cases h1 : I.entails .one φ <;> cases h2 : I.entails .one φ'
  · rfl
  · exact absurd (ent_trans (show I.Entails .one φ' from h2) h.2) (by simp [I.Entails, h1])
  · exact absurd (ent_trans (show I.Entails .one φ from h1) h.1) (by simp [I.Entails, h2])
  · rfl

theorem FEq.or {a a' b b' : I} (h1 : FEq a a') (h2 : FEq b b') : FEq (.or a b) (.or a' b') :=
  ⟨ent_or_elim (ent_trans h1.1 (ent_or_left _ _)) (ent_trans h2.1 (ent_or_right _ _)),
    ent_or_elim (ent_trans h1.2 (ent_or_left _ _)) (ent_trans h2.2 (ent_or_right _ _))⟩

theorem FEq.shift {a a' : I} (h : FEq a a') : FEq a.shift a'.shift := h.ren _

theorem FEq.forall0 {a a' : I} (h : FEq a a') : FEq a.forall0 a'.forall0 := by
  have m : ∀ {x y : I}, I.Entails x y → I.Entails x.forall0 y.forall0 := fun {x y} hxy =>
    entails_iff.2 fun ρ hρ hx => (forall0_sem hρ y).2 (entails_iff.1 hxy _ (consAsg_k3 (by decide) hρ) ((forall0_sem hρ x).1 hx))
  exact ⟨m h.1, m h.2⟩

macro "near" : tactic => `(tactic| repeat' (first
  | exact TmNear.refl _
  | exact FEq.refl _
  | exact I_eq_refl _
  | assumption
  | apply TmNear.pi | apply TmNear.lam | apply TmNear.app | apply TmNear.sigma | apply TmNear.pair
  | apply TmNear.fst | apply TmNear.snd | apply TmNear.path | apply TmNear.plam | apply TmNear.papp
  | apply TmNear.ipi | apply TmNear.split | apply TmNear.transp | apply TmNear.hcomp | apply TmNear.glue
  | apply TmNear.glueEl | apply TmNear.unglue | apply TmNear.tcons | apply TmNear.data | apply TmNear.elim
  | apply TmNear.shift | apply TmNear.dshift | apply TmNear.dinst | apply TmNear.inst | apply TmNear.ren
  | apply FEq.or | apply FEq.shift | apply FEq.forall0 | apply FEq.ren | apply FEq.subst2
  | apply near_comp | apply near_fill | apply near_transpFill | apply near_hfill
  | apply TmNear.dsubst | apply TmNear.subst
  | (intro i; exact I_eq_refl _)
  | (intro n; exact TmNear.refl _)
  | (intro n; rcases n with _ | n <;> simp only)))

theorem near_comp {C C' u u' u0 u0' : Tm} {ψ ψ' : I} (hC : TmNear C C') (hψ : FEq ψ ψ') (hu : TmNear u u')
    (hu0 : TmNear u0 u0') : TmNear (Tm.comp C ψ u u0) (Tm.comp C' ψ' u' u0') := by
  simp only [Tm.comp]; near

theorem near_hfill {A A' u u' u0 u0' : Tm} {ψ ψ' : I} (hA : TmNear A A') (hψ : FEq ψ ψ') (hu : TmNear u u')
    (hu0 : TmNear u0 u0') : TmNear (Tm.hfill A ψ u u0) (Tm.hfill A' ψ' u' u0') := by
  simp only [Tm.hfill]; near

theorem near_transpPi {A A' B B' a a' : Tm} {φ φ' : I} (hA : TmNear A A') (hB : TmNear B B') (hφ : FEq φ φ')
    (ha : TmNear a a') : TmNear (Tm.transpPi A B φ a) (Tm.transpPi A' B' φ' a') := by
  simp only [Tm.transpPi]; near

theorem near_transpFill {A A' a a' : Tm} {φ φ' : I} (hA : TmNear A A') (hφ : FEq φ φ') (ha : TmNear a a') :
    TmNear (Tm.transpFill A φ a) (Tm.transpFill A' φ' a') := by
  simp only [Tm.transpFill]; near

theorem near_fill {C C' u u' u0 u0' : Tm} {ψ ψ' : I} (hC : TmNear C C') (hψ : FEq ψ ψ') (hu : TmNear u u')
    (hu0 : TmNear u0 u0') : TmNear (Tm.fill C ψ u u0) (Tm.fill C' ψ' u' u0') := by
  simp only [Tm.fill, Tm.comp]; near

theorem near_transpSigma {A A' B B' a a' : Tm} {φ φ' : I} (hA : TmNear A A') (hB : TmNear B B') (hφ : FEq φ φ')
    (ha : TmNear a a') : TmNear (Tm.transpSigma A B φ a) (Tm.transpSigma A' B' φ' a') := by
  simp only [Tm.transpSigma, Tm.transpFill]; near

theorem near_transpPath {A A' x x' y y' a a' : Tm} {φ φ' : I} (hA : TmNear A A') (hx : TmNear x x')
    (hy : TmNear y y') (hφ : FEq φ φ') (ha : TmNear a a') :
    TmNear (Tm.transpPath A x y φ a) (Tm.transpPath A' x' y' φ' a') := by
  simp only [Tm.transpPath, Tm.comp]; near

theorem near_transpIPi {A A' a a' : Tm} {φ φ' : I} (hA : TmNear A A') (hφ : FEq φ φ') (ha : TmNear a a') :
    TmNear (Tm.transpIPi A φ a) (Tm.transpIPi A' φ' a') := by
  simp only [Tm.transpIPi]; near

theorem near_hcompPi {A A' B B' u u' a a' : Tm} {φ φ' : I} (hA : TmNear A A') (hB : TmNear B B') (hφ : FEq φ φ')
    (hu : TmNear u u') (ha : TmNear a a') : TmNear (Tm.hcompPi A B φ u a) (Tm.hcompPi A' B' φ' u' a') := by
  simp only [Tm.hcompPi]; near

theorem near_hcompSigma {A A' B B' u u' a a' : Tm} {φ φ' : I} (hA : TmNear A A') (hB : TmNear B B')
    (hφ : FEq φ φ') (hu : TmNear u u') (ha : TmNear a a') :
    TmNear (Tm.hcompSigma A B φ u a) (Tm.hcompSigma A' B' φ' u' a') := by
  simp only [Tm.hcompSigma, Tm.hfill, Tm.comp]; near

theorem near_hcompPath {A A' x x' y y' u u' a a' : Tm} {φ φ' : I} (hA : TmNear A A') (hx : TmNear x x')
    (hy : TmNear y y') (hφ : FEq φ φ') (hu : TmNear u u') (ha : TmNear a a') :
    TmNear (Tm.hcompPath A x y φ u a) (Tm.hcompPath A' x' y' φ' u' a') := by
  simp only [Tm.hcompPath]; near

theorem near_hcompIPi {A A' u u' a a' : Tm} {φ φ' : I} (hA : TmNear A A') (hφ : FEq φ φ') (hu : TmNear u u')
    (ha : TmNear a a') : TmNear (Tm.hcompIPi A φ u a) (Tm.hcompIPi A' φ' u' a') := by
  simp only [Tm.hcompIPi]; near

theorem near_hcompGlue {A A' T T' e e' u u' a a' : Tm} {φ φ' ψ ψ' : I} (hA : TmNear A A') (hφ : FEq φ φ')
    (hT : TmNear T T') (he : TmNear e e') (hψ : FEq ψ ψ') (hu : TmNear u u') (ha : TmNear a a') :
    TmNear (Tm.hcompGlue A φ T e ψ u a) (Tm.hcompGlue A' φ' T' e' ψ' u' a') := by
  simp only [Tm.hcompGlue, Tm.hfill]; near

theorem near_hcompU {u u' a a' : Tm} {φ φ' : I} (hφ : FEq φ φ') (hu : TmNear u u') (ha : TmNear a a') :
    TmNear (Tm.hcompU φ u a) (Tm.hcompU φ' u' a') := by
  simp only [Tm.hcompU, Tm.lineEquiv, Tm.lineFun, Tm.idIsEquiv, Tm.isEquiv, Tm.isContr, Tm.fiber]; near

set_option maxHeartbeats 4000000 in
theorem near_transpGlueWith {A A' T T' e e' a a' : Tm} {δ δ' φ φ' ψ ψ' : I} (hδ : FEq δ δ') (hA : TmNear A A')
    (hφ : FEq φ φ') (hT : TmNear T T') (he : TmNear e e') (hψ : FEq ψ ψ') (ha : TmNear a a') :
    TmNear (Tm.transpGlueWith δ A φ T e ψ a) (Tm.transpGlueWith δ' A' φ' T' e' ψ' a') := by
  simp only [Tm.transpGlueWith, Tm.fiber, Tm.pathC]; near

/-! ### Lists of near terms -/

abbrev NearL (L L' : List Tm) : Prop := List.Forall₂ TmNear L L'

theorem nearL_refl : ∀ (L : List Tm), NearL L L
  | [] => .nil
  | t :: L => .cons (TmNear.refl t) (nearL_refl L)

theorem toList_near {t t' : Tm} (h : TmNear t t') : NearL t.toList t'.toList := by
  induction h with
  | tcons h1 _ _ ih => exact .cons h1 ih
  | _ => exact .nil

theorem ofList_near {L L' : List Tm} (h : NearL L L') : TmNear (Tm.ofList L) (Tm.ofList L') := by
  induction h with
  | nil => exact .tnil
  | cons h1 _ ih => exact .tcons h1 ih

theorem nearL_append {L1 L1' L2 L2' : List Tm} (h1 : NearL L1 L1') (h2 : NearL L2 L2') :
    NearL (L1 ++ L2) (L1' ++ L2') := List.rel_append h1 h2

theorem nearL_reverse {L L' : List Tm} (h : NearL L L') : NearL L.reverse L'.reverse :=
  List.forall₂_reverse_iff.2 h

theorem nearL_map {L L' : List Tm} (h : NearL L L') {f g : Tm → Tm} (hfg : ∀ x x', TmNear x x' → TmNear (f x) (g x')) :
    NearL (L.map f) (L'.map g) := by
  induction h with
  | nil => exact .nil
  | cons h1 _ ih => exact .cons (hfg _ _ h1) ih

theorem nearL_getD {L L' : List Tm} (h : NearL L L') {d d' : Tm} (hd : TmNear d d') (j : ℕ) :
    TmNear (L.getD j d) (L'.getD j d') := by
  induction h generalizing j with
  | nil => exact hd
  | cons h1 _ ih => cases j with
    | zero => exact h1
    | succ j => exact ih j

theorem nearL_get? {L L' : List Tm} (h : NearL L L') (j : ℕ) : Option.Rel TmNear L[j]? L'[j]? := by
  induction h generalizing j with
  | nil => exact .none
  | cons h1 _ ih => cases j with
    | zero => exact .some h1
    | succ j => exact ih j

theorem nearL_length {L L' : List Tm} (h : NearL L L') : L.length = L'.length := h.length_eq

theorem near_substList {L L' : List Tm} (hL : NearL L L') {t t' : Tm} (ht : TmNear t t') :
    TmNear (t.substList L) (t'.substList L') := by
  unfold Tm.substList
  refine ht.subst (fun j => ?_) (fun i => I_eq_refl _)
  rw [nearL_length hL]
  exact nearL_getD hL (TmNear.refl _) j

theorem near_apps {f f' : Tm} (hf : TmNear f f') {L L' : List Tm} (hL : NearL L L') :
    TmNear (Tm.apps f L) (Tm.apps f' L') := by
  induction hL generalizing f f' with
  | nil => exact hf
  | cons h1 _ ih => exact ih (.app hf h1)

theorem near_papps {f f' : Tm} (hf : TmNear f f') {rs rs' : List I} (hrs : List.Forall₂ I.Eq rs rs') :
    TmNear (Tm.papps f rs) (Tm.papps f' rs') := by
  induction hrs generalizing f f' with
  | nil => exact hf
  | cons h1 _ ih => exact ih (.papp hf h1)

theorem near_transpTele (argTy : ℕ → Tm) {psL psL' : List Tm} (hps : NearL psL psL') {φ φ' : I} (hφ : FEq φ φ') :
    ∀ (k : ℕ) {fills fills' as as' : List Tm}, NearL fills fills' → NearL as as' →
      NearL (Tm.transpTele argTy psL φ k fills as) (Tm.transpTele argTy psL' φ' k fills' as') := by
  intro k fills fills' as as' hf has
  induction has generalizing k fills fills' with
  | nil => exact .nil
  | cons ha _ ih =>
    simp only [Tm.transpTele]
    have hL := near_substList (nearL_append hf (nearL_reverse hps)) (TmNear.refl (argTy k))
    exact .cons (.transp hL hφ ha) (ih (k + 1) (.cons (near_transpFill hL hφ ha) hf))

theorem nearL_map_same {α : Type} (L : List α) {f g : α → Tm} (h : ∀ x, TmNear (f x) (g x)) :
    NearL (L.map f) (L.map g) := by
  induction L with
  | nil => exact .nil
  | cons x L ih => exact .cons (h x) ih

theorem nearL_mapIdx {α : Type} (L : List α) : ∀ {f g : ℕ → α → Tm}, (∀ i x, TmNear (f i x) (g i x)) →
    NearL (L.mapIdx f) (L.mapIdx g) := by
  induction L with
  | nil => intro f g _; exact .nil
  | cons x L ih =>
    intro f g h
    rw [List.mapIdx_cons, List.mapIdx_cons]
    exact .cons (h 0 x) (ih fun i y => h (i + 1) y)

theorem ieqL_getD {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') (d : I) (j : ℕ) :
    I.Eq (rs.getD j d) (rs'.getD j d) := by
  induction h generalizing j with
  | nil => exact I_eq_refl _
  | cons h1 _ ih => cases j with
    | zero => exact h1
    | succ j => exact ih j

theorem ieqL_reverse {rs rs' : List I} (h : List.Forall₂ I.Eq rs rs') : List.Forall₂ I.Eq rs.reverse rs'.reverse :=
  List.forall₂_reverse_iff.2 h

theorem near_hcompTele (C : Ctor) (argTy : ℕ → Tm) {dT dT' : Tm} (hd : TmNear dT dT') {psL psL' : List Tm}
    (hps : NearL psL psL') {φ φ' : I} (hφ : FEq φ φ') :
    ∀ (k : ℕ) {fills fills' us us' as as' : List Tm}, NearL fills fills' → NearL us us' → NearL as as' →
      NearL (Tm.hcompTele C argTy dT psL φ k fills us as) (Tm.hcompTele C argTy dT' psL' φ' k fills' us' as') := by
  intro k fills fills' us us' as as' hf hus has
  induction hus generalizing k fills fills' as as' with
  | nil => cases has <;> exact .nil
  | cons hu _ ih =>
    cases has with
    | nil => exact .nil
    | cons ha has' =>
      simp only [Tm.hcompTele]
      split_ifs
      · exact .cons (.hcomp hd hφ hu ha) (ih (k + 1) (.cons (near_hfill hd hφ hu ha) hf) has')
      · have hL := near_substList (nearL_append hf (nearL_reverse hps)) (TmNear.refl (argTy k))
        exact .cons (near_comp hL hφ hu ha) (ih (k + 1) (.cons (near_fill hL hφ hu ha) hf) has')

theorem near_bndAt (b : Tm) {ps ps' args args' : List Tm} (hps : NearL ps ps') (hargs : NearL args args')
    {rs rs' : List I} (hrs : List.Forall₂ I.Eq rs rs') :
    TmNear (Ctor.bndAt b ps args rs) (Ctor.bndAt b ps' args' rs') := by
  unfold Ctor.bndAt
  exact (TmNear.refl b).subst (fun j => nearL_getD (nearL_append (nearL_reverse hargs) (nearL_reverse hps))
    (TmNear.refl _) j) (fun i => ieqL_getD (ieqL_reverse hrs) _ i)

theorem firstBnd_near (bnd : List (I × Tm)) {rs rs' : List I} (hrs : List.Forall₂ I.Eq rs rs') :
    firstBnd bnd rs = firstBnd bnd rs' := by
  unfold firstBnd
  have e : (fun p : I × Tm => I.entails .one (Ctor.cofAt p.1 rs)) = (fun p => I.entails .one (Ctor.cofAt p.1 rs')) := by
    funext p
    exact (FEq.of_eq (I_eq_subst_congr (fun i => ieqL_getD (ieqL_reverse hrs) _ i) p.1)).entails
  rw [e]

theorem near_lams {Ts Ts' : List Tm} (hT : NearL Ts Ts') {b b' : Tm} (hb : TmNear b b') :
    TmNear (Model.Canon.lams Ts b) (Model.Canon.lams Ts' b') := by
  unfold Model.Canon.lams
  induction hT with
  | nil => exact hb
  | cons h1 _ ih => exact .lam h1 ih

theorem near_branchesOf (D : DataDecl) (d : ℕ) {ps ps' P P' : Tm} (hps : TmNear ps ps') (hP : TmNear P P')
    {body body' : ℕ → Ctor → Tm} (hb : ∀ c C, TmNear (body c C) (body' c C)) :
    TmNear (Model.Canon.branchesOf D d ps P body) (Model.Canon.branchesOf D d ps' P' body') := by
  unfold Model.Canon.branchesOf
  refine ofList_near (nearL_mapIdx _ fun c C => near_lams (nearL_append ?_ ?_) (hb c C))
  · refine nearL_map_same _ fun k => ?_
    unfold DataDecl.branchArgTy
    exact near_substList (nearL_append (nearL_refl _) (nearL_map (nearL_reverse (toList_near hps))
      fun x x' hx => hx.ren _ _)) (TmNear.refl _)
  · refine nearL_map_same _ fun s => ?_
    unfold DataDecl.branchIhTy
    exact hP.subst (fun n => TmNear.refl _) (fun i => I_eq_refl _)

theorem near_proj (d : ℕ) (D : DataDecl) {ps ps' : Tm} (hps : TmNear ps ps') (c : ℕ) (C : Ctor) (j : ℕ) {t t' : Tm}
    (ht : TmNear t t') : TmNear (Model.Canon.proj d D ps c C j t) (Model.Canon.proj d D ps' c C j t') := by
  have hQ : TmNear (Model.Canon.projQ d D ps c C j) (Model.Canon.projQ d D ps' c C j) := by
    unfold Model.Canon.projQ
    refine .elim hps (TmNear.refl _) (near_branchesOf D d hps (TmNear.refl _) fun c' C' => ?_) (TmNear.refl _)
    unfold Model.Canon.projQBody
    split_ifs
    · exact near_substList (nearL_append (nearL_refl _) (nearL_reverse (toList_near hps))) (TmNear.refl _)
    · exact .pi (.data hps) (.data hps)
  unfold Model.Canon.proj
  refine .elim hps hQ (near_branchesOf D d hps hQ fun c' C' => ?_) ht
  unfold Model.Canon.projBody
  split_ifs
  · exact TmNear.refl _
  · exact .lam (.data hps) (TmNear.refl _)

theorem rel_map {o o' : Option Tm} (h : Option.Rel TmNear o o') {f g : Tm → Tm}
    (hfg : ∀ x x', TmNear x x' → TmNear (f x) (g x')) : Option.Rel TmNear (o.map f) (o'.map g) := by
  cases h with
  | none => exact .none
  | some h => exact .some (hfg _ _ h)

theorem rel_isNone {o o' : Option Tm} (h : Option.Rel TmNear o o') : o = none ↔ o' = none := by
  cases h <;> simp

theorem step_app_eq (S : Sig) (f a : Tm) (hf : ∀ A t, f ≠ .lam A t) :
    step S (.app f a) = (step S f).map (.app · a) := by
  cases f <;> simp_all [step]

theorem step_fst_eq (S : Sig) (p : Tm) (hp : ∀ a b, p ≠ .pair a b) : step S (.fst p) = (step S p).map .fst := by
  cases p <;> simp_all [step]

theorem step_snd_eq (S : Sig) (p : Tm) (hp : ∀ a b, p ≠ .pair a b) : step S (.snd p) = (step S p).map .snd := by
  cases p <;> simp_all [step]

theorem step_papp_eq (S : Sig) (p : Tm) (r : I) (hp : ∀ t, p ≠ .plam t) :
    step S (.papp p r) = (step S p).map (.papp · r) := by
  cases p <;> simp_all [step]

theorem near_lam_iff {f f' : Tm} (h : TmNear f f') : (∃ A t, f = .lam A t) ↔ (∃ A t, f' = .lam A t) := by
  cases h <;> simp

theorem near_pair_iff {f f' : Tm} (h : TmNear f f') : (∃ a b, f = .pair a b) ↔ (∃ a b, f' = .pair a b) := by
  cases h <;> simp

theorem near_plam_iff {f f' : Tm} (h : TmNear f f') : (∃ t, f = .plam t) ↔ (∃ t, f' = .plam t) := by
  cases h <;> simp

theorem rel_refl (o : Option Tm) : Option.Rel TmNear o o := by
  cases o with
  | none => exact .none
  | some x => exact .some (TmNear.refl x)

/-- Reduction respects nearness. -/
theorem step_near (S : Sig) {t t' : Tm} (h : TmNear t t') : Option.Rel TmNear (step S t) (step S t') := by
  induction h with
  | var => exact rel_refl _
  | const => exact rel_refl _
  | univ => exact rel_refl _
  | abort => exact rel_refl _
  | tnil => exact rel_refl _
  | pi => exact .none
  | lam => exact .none
  | sigma => exact .none
  | pair => exact .none
  | path => exact .none
  | plam => exact .none
  | ipi => exact .none
  | tcons => exact .none
  | data => exact .none
  | @app f f' a a' hf ha ihf _ =>
    by_cases hl : ∃ A t, f = .lam A t
    · obtain ⟨A, t, rfl⟩ := hl
      cases hf with | lam _ ht => exact .some (ht.inst ha)
    · have hl' : ¬ ∃ A t, f' = .lam A t := fun h => hl ((near_lam_iff hf).2 h)
      rw [step_app_eq S f a (fun A t e => hl ⟨A, t, e⟩), step_app_eq S f' a' (fun A t e => hl' ⟨A, t, e⟩)]
      exact rel_map ihf fun x x' hx => .app hx ha
  | @fst p p' hp ihp =>
    by_cases hl : ∃ a b, p = .pair a b
    · obtain ⟨a, b, rfl⟩ := hl
      cases hp with | pair h1 _ => exact .some h1
    · have hl' : ¬ ∃ a b, p' = .pair a b := fun h => hl ((near_pair_iff hp).2 h)
      rw [step_fst_eq S p (fun a b e => hl ⟨a, b, e⟩), step_fst_eq S p' (fun a b e => hl' ⟨a, b, e⟩)]
      exact rel_map ihp fun x x' hx => .fst hx
  | @snd p p' hp ihp =>
    by_cases hl : ∃ a b, p = .pair a b
    · obtain ⟨a, b, rfl⟩ := hl
      cases hp with | pair _ h2 => exact .some h2
    · have hl' : ¬ ∃ a b, p' = .pair a b := fun h => hl ((near_pair_iff hp).2 h)
      rw [step_snd_eq S p (fun a b e => hl ⟨a, b, e⟩), step_snd_eq S p' (fun a b e => hl' ⟨a, b, e⟩)]
      exact rel_map ihp fun x x' hx => .snd hx
  | @papp p p' r r' hp hr ihp =>
    by_cases hl : ∃ t, p = .plam t
    · obtain ⟨t, rfl⟩ := hl
      cases hp with | plam ht => exact .some (ht.dinst hr)
    · have hl' : ¬ ∃ t, p' = .plam t := fun h => hl ((near_plam_iff hp).2 h)
      rw [step_papp_eq S p r (fun t e => hl ⟨t, e⟩), step_papp_eq S p' r' (fun t e => hl' ⟨t, e⟩)]
      exact rel_map ihp fun x x' hx => .papp hx hr
  | @split φ φ' ψ ψ' t t' u u' e1 ht e2 hu _ _ =>
    show Option.Rel TmNear (if I.entails .one φ then some t else if I.entails .one ψ then some u else none)
      (if I.entails .one φ' then some t' else if I.entails .one ψ' then some u' else none)
    rw [e1.entails, e2.entails]
    split_ifs
    · exact .some ht
    · exact .some hu
    · exact .none
  | @glue A A' T T' e e' φ φ' _ hφ hT _ _ _ _ =>
    show Option.Rel TmNear (if I.entails .one φ then some T else none) (if I.entails .one φ' then some T' else none)
    rw [hφ.entails]
    split_ifs
    · exact .some hT
    · exact .none
  | @glueEl e e' t t' a a' φ φ' hφ _ ht _ _ _ _ =>
    show Option.Rel TmNear (if I.entails .one φ then some t else none) (if I.entails .one φ' then some t' else none)
    rw [hφ.entails]
    split_ifs
    · exact .some ht
    · exact .none
  | @unglue e e' g g' φ φ' hφ he hg _ ihg =>
    simp only [step]
    rw [hφ.entails]
    split_ifs
    · exact .some (.app (.fst he) hg)
    · generalize step S g = o at ihg ⊢
      generalize step S g' = o' at ihg ⊢
      cases ihg with
      | some hx => exact .some (.unglue hφ he hx)
      | none =>
        cases hg with
        | glueEl _ _ _ h4 => exact .some h4
        | _ => exact .none
  | @transp A A' a a' φ φ' hA hφ ha ihA iha =>
    simp only [step]
    rw [hφ.entails]
    split_ifs
    · exact .some ha
    · generalize step S A = o at ihA ⊢
      generalize step S A' = o' at ihA ⊢
      cases ihA with
      | some hx => exact .some (.transp hx hφ ha)
      | none =>
        cases hA with
        | univ => exact .some ha
        | pi h1 h2 => exact .some (near_transpPi h1 h2 hφ ha)
        | sigma h1 h2 => exact .some (near_transpSigma h1 h2 hφ ha)
        | path h1 h2 h3 => exact .some (near_transpPath h1 h2 h3 hφ ha)
        | ipi h1 => exact .some (near_transpIPi h1 hφ ha)
        | glue h1 h2 h3 h4 => exact .some (near_transpGlueWith h2.forall0 h1 h2 h3 h4 hφ ha)
        | @data d ps ps' hps =>
          simp only
          generalize S[d]? = oD
          rcases oD with _ | ⟨_ | D⟩
          · exact .none
          · exact .none
          · simp only
            split_ifs
            · exact .some ha
            · generalize step S a = o at iha ⊢
              generalize step S a' = o' at iha ⊢
              cases iha with
              | some hx => exact .some (.transp (.data hps) hφ hx)
              | none =>
                cases ha with
                | @con d1 c ps1 ps1' args args' rs rs' hps1 hargs hrs =>
                  simp only
                  split_ifs
                  · exact .none
                  · generalize D.ctors[c]? = oC
                    rcases oC with _ | C
                    · exact .none
                    · exact .some (.con (hps.dinst (I_eq_refl _)) (ofList_near (near_transpTele _
                        (toList_near hps) hφ 0 .nil (toList_near hargs))) hrs)
                | @hcomp X X' ψ ψ' u u' b b' hX hψ hu hb =>
                  cases hX with
                  | data hps0 =>
                    simp only
                    split_ifs
                    · exact .some (by near)
                    · exact .none
                  | _ => exact .none
                | _ => exact .none
        | _ => exact .none
  | @hcomp A A' u u' a a' φ φ' hA hφ hu ha ihA _ iha =>
    simp only [step]
    rw [hφ.entails]
    split_ifs
    · exact .some (hu.dinst (I_eq_refl _))
    · generalize step S A = o at ihA ⊢
      generalize step S A' = o' at ihA ⊢
      cases ihA with
      | some hx => exact .some (.hcomp hx hφ hu ha)
      | none =>
        cases hA with
        | univ => exact .some (near_hcompU hφ hu ha)
        | pi h1 h2 => exact .some (near_hcompPi h1 h2 hφ hu ha)
        | sigma h1 h2 => exact .some (near_hcompSigma h1 h2 hφ hu ha)
        | path h1 h2 h3 => exact .some (near_hcompPath h1 h2 h3 hφ hu ha)
        | ipi h1 => exact .some (near_hcompIPi h1 hφ hu ha)
        | glue h1 h2 h3 h4 => exact .some (near_hcompGlue h1 h2 h3 h4 hφ hu ha)
        | @data d ps ps' hps =>
          simp only
          generalize S[d]? = oD
          rcases oD with _ | ⟨_ | D⟩
          · exact .none
          · exact .none
          · simp only
            split_ifs
            · exact .none
            · generalize step S a = o at iha ⊢
              generalize step S a' = o' at iha ⊢
              cases iha with
              | some hx => exact .some (.hcomp (.data hps) hφ hu hx)
              | none =>
                cases ha with
                | @con d1 c ps1 ps1' args args' rs rs' hps1 hargs hrs =>
                  cases hrs with
                  | nil =>
                    simp only
                    split_ifs
                    · exact .none
                    · generalize D.ctors[c]? = oC
                      rcases oC with _ | C
                      · exact .none
                      · exact .some (.con hps (ofList_near (near_hcompTele C _ (.data hps) (toList_near hps.dshift) hφ 0
                          .nil (nearL_map_same _ fun j => near_proj d D hps.dshift c C j hu) (toList_near hargs))) .nil)
                  | cons _ _ => exact .none
                | _ => exact .none
        | _ => exact .none
  | @con d c ps ps' args args' rs rs' hps hargs hrs _ _ =>
    simp only [step]
    generalize S[d]? = oD
    rcases oD with _ | ⟨_ | D⟩
    · exact .none
    · exact .none
    · simp only
      generalize D.ctors[c]? = oC
      rcases oC with _ | C
      · exact .none
      · simp only
        rw [firstBnd_near C.bnd hrs]
        generalize firstBnd C.bnd rs' = ob
        rcases ob with _ | b
        · exact .none
        · exact .some (near_bndAt b (toList_near hps) (toList_near hargs) hrs)
  | @elim d ps ps' P P' bs bs' t t' hps hP hbs ht _ _ _ iht =>
    simp only [step]
    generalize step S t = o at iht ⊢
    generalize step S t' = o' at iht ⊢
    cases iht with
    | some hx => exact .some (.elim hps hP hbs hx)
    | none =>
      cases ht with
      | @con d1 c ps1 ps1' args args' rs rs' hps1 hargs hrs =>
        simp only
        split_ifs
        · exact .none
        · have hb := nearL_get? (toList_near hbs) c
          generalize S[d]? = oD
          generalize bs.toList[c]? = ob at hb ⊢
          generalize bs'.toList[c]? = ob' at hb ⊢
          rcases oD with _ | ⟨_ | D⟩
          · exact .none
          · cases hb <;> exact .none
          · cases hb with
            | none => exact .none
            | some hb =>
              simp only
              generalize D.ctors[c]? = oC
              rcases oC with _ | C
              · exact .none
              · exact .some (near_papps (near_apps hb (nearL_append (toList_near hargs)
                  (nearL_map_same _ fun k => .elim hps hP hbs (nearL_getD (toList_near hargs) .abort k)))) hrs)
      | @hcomp X X' φ φ' u u' a a' hX hφ hu ha =>
        cases hX with
        | data hps0 =>
          simp only
          generalize S[d]? = oD
          rcases oD with _ | ⟨_ | D⟩
          · exact .none
          · exact .none
          · simp only
            split_ifs
            · exact .some (by near)
            · exact .none
        | _ => exact .none
      | _ => exact .none
