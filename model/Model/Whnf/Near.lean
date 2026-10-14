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
  | apply TmNear.glueEl | apply TmNear.unglue | apply TmNear.tcons | apply TmNear.data
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

end Model.Whnf
