import Model.Whnf.Step
import KubusCore.Meta.Near

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

theorem near_papps {f f' : Tm} (hf : TmNear f f') {rs rs' : List I} (hrs : IEqL rs rs') :
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

theorem ieqL_getD {rs rs' : List I} (h : IEqL rs rs') (d : I) (j : ℕ) :
    I.Eq (rs.getD j d) (rs'.getD j d) := by
  induction h generalizing j with
  | nil => exact I_eq_refl _
  | cons h1 _ ih => cases j with
    | zero => exact h1
    | succ j => exact ih j

theorem ieqL_iff {rs rs' : List I} : IEqL rs rs' ↔ List.Forall₂ I.Eq rs rs' := by
  constructor
  · intro h; induction h with
    | nil => exact .nil
    | cons e _ ih => exact .cons e ih
  · intro h; induction h with
    | nil => exact .nil
    | cons e _ ih => exact .cons e ih

theorem ieqL_reverse {rs rs' : List I} (h : IEqL rs rs') : IEqL rs.reverse rs'.reverse :=
  ieqL_iff.2 (List.forall₂_reverse_iff.2 (ieqL_iff.1 h))

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
    {rs rs' : List I} (hrs : IEqL rs rs') :
    TmNear (Ctor.bndAt b ps args rs) (Ctor.bndAt b ps' args' rs') := by
  unfold Ctor.bndAt
  exact (TmNear.refl b).subst (fun j => nearL_getD (nearL_append (nearL_reverse hargs) (nearL_reverse hps))
    (TmNear.refl _) j) (fun i => ieqL_getD (ieqL_reverse hrs) _ i)

theorem firstBnd_near (bnd : List (I × Tm)) {rs rs' : List I} (hrs : IEqL rs rs') :
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
