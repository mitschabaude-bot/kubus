import Model.Whnf.Fund2

/-!
# Validity of the rules of inductive types

The binary counterpart of `Model/Canon/FormersData.lean`, `Model/Canon/Final.lean` (`csub_params`,
`csub_points`): related parameters and earlier point arguments as related substitutions out of the
parameter and point contexts, and the relation of literal inductive types at related parameters.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

/-- The declared types of the inductive types before `n` are valid: the parameter types in their
parameter contexts, and the point argument types in their point contexts. -/
structure DeclHyp2 (S : Sig) (n : ℕ) : Prop where
  params : ∀ d < n, ∀ (D : DataDecl), S[d]? = some (.data D) → ∀ (j : ℕ) (A : Tm), D.params[j]? = some A →
    ∀ k (c : CSub2 S 0 .one (D.paramCtx j) k), RT2 S k (c.L A) (c.R A)
  points : ∀ d < n, ∀ (D : DataDecl), S[d]? = some (.data D) → ∀ (c : ℕ) (C : Ctor), D.ctors[c]? = some C →
    ∀ (i : ℕ) (A : Tm), C.args[i]? = some (.point A) →
    ∀ k (cs : CSub2 S 0 .one (D.pointCtx d C i) k), RT2 S k (cs.L (A.ren (C.pointRen i) id)) (cs.R (A.ren (C.pointRen i) id))

/-- The interval substitution out of the empty interval context. -/
def ISub.none0 (k : ℕ) : ISub k 0 := ⟨fun _ => .zero, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩

/-- The related substitution out of the empty parameter context. -/
def CSub2.nil0 (S : Sig) (D : DataDecl) (k : ℕ) : CSub2 S 0 .one (D.paramCtx 0) k where
  σ := ISub.none0 k
  σ' := ISub.none0 k
  hσ := INear.refl _
  γ := lsub [] 0
  γ' := lsub [] 0
  hγ _ := rfl
  hγ' _ := rfl
  face := ent_refl _
  look x A h := by simp [DataDecl.paramCtx, Ctx.lookup] at h
  lookT x A h := by simp [DataDecl.paramCtx, Ctx.lookup] at h

theorem take_succ_rev (L : List Tm) {j : ℕ} (h : j < L.length) :
    (L.take (j + 1)).reverse = L[j] :: (L.take j).reverse := by
  rw [List.take_succ, List.getElem?_eq_getElem h]; simp

variable (hW : WfSig S)
include hW

theorem lsub_closed_isub (L : List Tm) (hL : ∀ t ∈ L, t.closedB 0 k = true) (y : ℕ) :
    (lsub L 0 y).isub (ISub.id k) = lsub L 0 y := by
  simp only [lsub, List.getD_eq_getElem?_getD]
  cases h : L[y]? with
  | none => rfl
  | some t =>
    obtain ⟨hy, rfl⟩ := List.getElem?_eq_some_iff.1 h
    exact isub_id_of_closed (hL _ (List.getElem_mem hy))

/-- Related parameters, related at their types instantiated by the earlier left parameters, as
related substitutions out of the parameter contexts. -/
theorem csub2_params {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : DeclHyp2 S (d + 1))
    {ps ps' : List Tm} (hpl : ps.length = D.params.length) (hpl' : ps'.length = D.params.length)
    (hps : ∀ j (hj : j < ps.length) (hj' : j < ps'.length) (hjD : j < D.params.length),
      RE2 S k (D.params[j].substList (ps.take j).reverse) ps[j] ps'[j]) :
    ∀ j, j ≤ D.params.length → ∃ c : CSub2 S 0 .one (D.paramCtx j) k,
      c.γ = lsub (ps.take j).reverse 0 ∧ c.γ' = lsub (ps'.take j).reverse 0 ∧ c.σ = ISub.none0 k ∧ c.σ' = ISub.none0 k
  | 0, _ => by
    refine ⟨CSub2.nil0 S D k, ?_, ?_, rfl, rfl⟩ <;> simp [CSub2.nil0]
  | j + 1, hj => by
    obtain ⟨c, hcγ, hcγ', hcσ, hcσ'⟩ := csub2_params hD hH hpl hpl' hps j (by omega)
    have hjp : j < D.params.length := by omega
    have hcl : (D.params[j]).closedB ((ps.take j).reverse).length 0 = true := by
      have := params_closed (sigClosed_of_wfSig hW) hD j _ (List.getElem?_eq_getElem hjp)
      simpa [Nat.min_eq_left (show j ≤ ps.length by omega)] using this
    have hA : RE2 S k (c.L D.params[j]) ps[j] ps'[j] := by
      show RE2 S k ((D.params[j]).subst c.γ c.σ.τ) _ _
      rw [hcγ, subst_lsub_closed hcl]; exact hps j (by omega) (by omega) hjp
    have hRob := CSub2.tyRob_of hW (hH.params d (by omega) D hD j _ (List.getElem?_eq_getElem hjp)) c
    rw [paramCtx_succ D hjp]
    refine ⟨c.ext hW _ _ _ hA hRob, ?_, ?_, hcσ, hcσ'⟩
    · show consT ps[j] c.γ = _
      rw [hcγ, consT_lsub]
      congr 1
      exact (take_succ_rev ps (by omega)).symm
    · show consT ps'[j] c.γ' = _
      rw [hcγ', consT_lsub]
      congr 1
      exact (take_succ_rev ps' (by omega)).symm

/-- Related parameters and earlier point arguments as related substitutions out of the point contexts. -/
theorem csub2_points {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : DeclHyp2 S (d + 1)) {c : ℕ}
    {C : Ctor} (hC : D.ctors[c]? = some C) {ps ps' args args' : List Tm}
    (hpl : ps.length = D.params.length) (hpl' : ps'.length = D.params.length)
    (hps : ∀ j (hj : j < ps.length) (hj' : j < ps'.length) (hjD : j < D.params.length),
      RE2 S k (D.params[j].substList (ps.take j).reverse) ps[j] ps'[j])
    (hlen : args.length ≤ C.args.length) (hlen' : args'.length = args.length)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), C.isRec i = false →
      RE2 S k ((C.argTy d D.params.length i).substList ((args.take i).reverse ++ ps.reverse)) args[i] args'[i]) :
    ∀ i, i ≤ args.length → ∃ cs : CSub2 S 0 .one (D.pointCtx d C i) k,
      cs.γ = lsub (ptL C args ps.reverse i) 0 ∧ cs.γ' = lsub (ptL C args' ps'.reverse i) 0 ∧
      cs.σ = ISub.none0 k ∧ cs.σ' = ISub.none0 k
  | 0, _ => by
    obtain ⟨c', hγ, hγ', hσ, hσ'⟩ := csub2_params hW hD hH hpl hpl' hps D.params.length (Nat.le_refl _)
    have hpc : D.pointCtx d C 0 = D.paramCtx D.params.length := by simp [DataDecl.pointCtx]
    rw [hpc]
    refine ⟨c', ?_, ?_, hσ, hσ'⟩
    · rw [hγ, List.take_of_length_le (by omega)]; rfl
    · rw [hγ', List.take_of_length_le (by omega)]; rfl
  | i + 1, hi => by
    obtain ⟨c', hγ, hγ', hσ, hσ'⟩ := csub2_points hD hH hC hpl hpl' hps hlen hlen' hargs i (by omega)
    rw [pointCtx_succ]
    by_cases hr' : C.isRec i = true
    · rw [if_pos hr']
      refine ⟨c', ?_, ?_, hσ, hσ'⟩
      · rw [hγ]; simp [ptL, hr']
      · rw [hγ']; simp [ptL, hr']
    · have hr : C.isRec i = false := by simpa using hr'
      rw [if_neg hr']
      have hiC : i < C.args.length := by omega
      obtain ⟨A0, hA0⟩ := point_of_not_rec hiC hr
      have hAk : C.argTy d D.params.length i = A0 := by simp [Ctor.argTy, hA0]
      have hA : RE2 S k (c'.L ((C.argTy d D.params.length i).ren (C.pointRen i) id)) args[i] args'[i] := by
        show RE2 S k (((C.argTy d D.params.length i).ren (C.pointRen i) id).subst c'.γ c'.σ.τ) _ _
        rw [hγ, hAk, pt_inst hW hD hC hA0 (by omega) (by simp [hpl]) 0 c'.σ.τ]
        have := hargs i (by omega) (by omega) hr
        rwa [hAk] at this
      have hRob := CSub2.tyRob_of hW (A := (C.argTy d D.params.length i).ren (C.pointRen i) id)
        (by rw [hAk]; exact hH.points d (by omega) D hD c C hC i A0 hA0) c'
      refine ⟨c'.ext hW _ _ _ hA hRob, ?_, ?_, hσ, hσ'⟩
      · show consT args[i] c'.γ = _
        rw [hγ, consT_lsub]
        simp only [ptL, hr, Bool.false_eq_true, if_false, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show i < args.length by omega), Option.getD_some]
        try rfl
      · show consT args'[i] c'.γ' = _
        rw [hγ', consT_lsub]
        simp only [ptL, hr, Bool.false_eq_true, if_false, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show i < args'.length by omega), Option.getD_some]
        try rfl

/-! ### Related parameter lists -/

/-- Parameter lists related at their types, instantiated by the earlier left parameters. -/
def ParRel2 (S : Sig) (k : ℕ) (D : DataDecl) (ps ps' : List Tm) : Prop :=
  ps.length = D.params.length ∧ ps'.length = D.params.length ∧
    ∀ j (hj : j < ps.length) (hj' : j < ps'.length) (hjD : j < D.params.length),
      RE2 S k (D.params[j].substList (ps.take j).reverse) ps[j] ps'[j]

omit hW in
theorem natural_of_eq {t u A : Tm} (hW : WfSig S) (h : EqTm S k .one [] t u A) :
    Natural S t k (idEnv k) (γ0 k) ∧ Natural S u k (idEnv k) (γ0 k) := by
  have e := presup hW (spec_to_minimal_eq hW h)
  exact ⟨natural_of_ty hW (minimal_to_spec e.1), natural_of_ty hW (minimal_to_spec e.2)⟩

/-- Substitution instances at elementwise judgmentally equal lists have equal values. -/
theorem semK_substList_congr (A : Tm) {L L' : List Tm} (hl : L.length = L'.length)
    (hL : ∀ i (hi : i < L.length) (hi' : i < L'.length), ∃ T, EqTm S k .one [] L[i] L'[i] T) :
    semK S k (A.substList L) = semK S k (A.substList L') := by
  have hn : ∀ (L0 : List Tm), (∀ t ∈ L0, Natural S t k (idEnv k) (γ0 k)) →
      ∀ x, Natural S ((fun j => L0.getD j (.var (j - L0.length))) x) k (idEnv k) (γ0 k) :=
    fun L0 h => natural_substList h
  have hL1 : ∀ t ∈ L, Natural S t k (idEnv k) (γ0 k) := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨T, e⟩ := hL i hi (by omega)
    exact (natural_of_eq hW e).1
  have hL2 : ∀ t ∈ L', Natural S t k (idEnv k) (γ0 k) := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨T, e⟩ := hL i (by omega) hi
    exact (natural_of_eq hW e).2
  unfold semK Tm.substList
  rw [sem_subst S A k _ _ _ _ (hn L hL1), sem_subst S A k _ _ _ _ (hn L' hL2)]
  congr 1; funext x
  simp only [List.getD_eq_getElem?_getD]
  by_cases hx : x < L.length
  · rw [List.getElem?_eq_getElem hx, List.getElem?_eq_getElem (show x < L'.length by omega)]
    obtain ⟨T, e⟩ := hL x hx (by omega)
    exact semK_eq hW e
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega), hl]

variable {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : DeclHyp2 S (d + 1))
include hD hH

/-- Related parameters have related parameter types. -/
theorem ParRel2.ty {ps ps' : List Tm} (h : ParRel2 S k D ps ps') (j : ℕ) (hjD : j < D.params.length) :
    RT2 S k (D.params[j].substList (ps.take j).reverse) (D.params[j].substList (ps'.take j).reverse) := by
  obtain ⟨hl, hl', hr⟩ := h
  obtain ⟨c, hcγ, hcγ', -, -⟩ := csub2_params hW hD hH hl hl' hr j hjD.le
  have hcl : ∀ L : List Tm, L.length = j → (D.params[j]).closedB L.length 0 = true := by
    intro L hL
    have := params_closed (sigClosed_of_wfSig hW) hD j _ (List.getElem?_eq_getElem hjD)
    simpa [hL] using this
  have := hH.params d (by omega) D hD j _ (List.getElem?_eq_getElem hjD) k c
  show RT2 S k _ _
  have e1 : c.L D.params[j] = D.params[j].substList (ps.take j).reverse := by
    show (D.params[j]).subst c.γ c.σ.τ = _
    rw [hcγ, subst_lsub_closed (hcl _ (by simp; omega))]
  have e2 : c.R D.params[j] = D.params[j].substList (ps'.take j).reverse := by
    show (D.params[j]).subst c.γ' c.σ'.τ = _
    rw [hcγ', subst_lsub_closed (hcl _ (by simp; omega))]
  rwa [e1, e2] at this

theorem ParRel2.symm {ps ps' : List Tm} (h : ParRel2 S k D ps ps') : ParRel2 S k D ps' ps := by
  refine ⟨h.2.1, h.1, fun j hj hj' hjD => ?_⟩
  have hT := h.ty hW hD hH j hjD
  exact RE2.conv hW hT (RE2.symm hW hT (h.2.2 j hj' hj hjD))

theorem ParRel2.left {ps ps' : List Tm} (h : ParRel2 S k D ps ps') : ParRel2 S k D ps ps := by
  refine ⟨h.1, h.1, fun j hj _ hjD => ?_⟩
  have hT := h.ty hW hD hH j hjD
  have e := h.2.2 j hj (by rw [h.2.1]; exact hjD) hjD
  exact RE2.trans hW hT e (RE2.symm hW hT e)

theorem ParRel2.right {ps ps' : List Tm} (h : ParRel2 S k D ps ps') : ParRel2 S k D ps' ps' :=
  (h.symm hW hD hH).left hW hD hH

/-- Related parameters and point arguments have related argument types. -/
theorem argTy_rel {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {ps ps' args args' : List Tm}
    (hp : ParRel2 S k D ps ps') (hlt : args.length < C.args.length) (hl' : args'.length = args.length)
    (hr : C.isRec args.length = false)
    (hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), C.isRec i = false →
      RE2 S k ((C.argTy d D.params.length i).substList ((args.take i).reverse ++ ps.reverse)) args[i] args'[i]) :
    RT2 S k ((C.argTy d D.params.length args.length).substList (args.reverse ++ ps.reverse))
      ((C.argTy d D.params.length args.length).substList (args'.reverse ++ ps'.reverse)) := by
  obtain ⟨A0, hA0⟩ := point_of_not_rec hlt hr
  have hAk : C.argTy d D.params.length args.length = A0 := by simp [Ctor.argTy, hA0]
  obtain ⟨cs, hγ, hγ', -, -⟩ := csub2_points hW hD hH hC hp.1 hp.2.1 hp.2.2 hlt.le hl' hargs args.length (Nat.le_refl _)
  have := hH.points d (by omega) D hD c C hC args.length A0 hA0 k cs
  have e1 : cs.L (A0.ren (C.pointRen args.length) id) = A0.substList (args.reverse ++ ps.reverse) := by
    show (A0.ren (C.pointRen args.length) id).subst cs.γ cs.σ.τ = _
    rw [hγ, pt_inst hW hD hC hA0 (Nat.le_refl _) (by simp [hp.1]) 0 cs.σ.τ, List.take_length]
  have e2 : cs.R (A0.ren (C.pointRen args.length) id) = A0.substList (args'.reverse ++ ps'.reverse) := by
    show (A0.ren (C.pointRen args.length) id).subst cs.γ' cs.σ'.τ = _
    rw [hγ', pt_inst hW hD hC hA0 (xs := args') (by omega) (by simp [hp.2.1]) 0 cs.σ'.τ,
      List.take_of_length_le (by omega)]
  rw [hAk]
  rwa [e1, e2] at this

/-! ### The relation of literal inductive types -/

omit hH in
theorem tyLook_code {X : Tm} {l k'' : ℕ} (hX : HasTy S k'' .one [] (.data d X) (.univ l)) (hxl : X = Tm.ofList X.toList)
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {j : ℕ} {A : Tm} (hA : C.args[j]? = some (.point A))
    {pre : List Tm} (hlen : pre.length = j) (hnat : ∀ t ∈ pre, Natural S t k'' (idEnv k'') (γ0 k''))
    (hv : ValidPre (ΘK S D d k'' X) c j (pre.map (semK S k''))) :
    tyLook (shapeV (ΘK S D d k'' X)) c j (pre.map (semK S k'')) =
      semK S k'' ((C.argTy d D.params.length j).substList (pre.reverse ++ X.toList.reverse)) := by
  rw [tyLook_eq hv, ΘK_ty_id hW hD hX hxl hC hA hlen hnat (ptValid_of_validPre hv)]

omit hW hD hH in
theorem validPre2_of_el {n : ℕ} {Λ : SData n} {c j : ℕ} {pre : List V} {k : ℕ} {A t t' : Tm}
    (h : (Comp2 S (tyLook (shapeV Λ) c j pre) k k (Hom.id k)).el A t t') : ValidPre Λ c j pre := by
  rcases tyLook_cases Λ c j pre with h0 | h0
  · rw [h0, Comp2_empty] at h; exact h.elim
  · exact h0

omit hD hH in
theorem DR2.memL {m k : ℕ} {d : ℕ} {D : DataDecl} {Mem : (k : ℕ) → Hom k m → Tm → Prop}
    {P : (k : ℕ) → Hom k m → ℕ → ℕ → List V → Tm → Tm → Tm → Prop} {f : Hom k m} {A t t' : Tm}
    (h : DR2 S d D Mem P k f A t t') : Mem k f t := by
  cases h with
  | intro he h2 _ _ =>
    have := h2 k (ISub.id k)
    rw [ISub.hom_id, Hom.comp_id, isub_id_of_closed (closed_of_ty hW (minimal_to_spec
      (presup hW (spec_to_minimal_eq hW he)).1))] at this
    cases this with
    | con hm => exact hm
    | hcomp hm => exact hm

/-- Elementwise judgmentally equal lists. -/
def ListEq (S : Sig) (k : ℕ) (L L' : List Tm) : Prop :=
  List.Forall₂ (fun a b => ∃ T, EqTm S k .one [] a b T) L L'

omit hW hD hH in
theorem ListEq.get {L L' : List Tm} (h : ListEq S k L L') :
    L.length = L'.length ∧ ∀ i (hi : i < L.length) (hi' : i < L'.length), ∃ T, EqTm S k .one [] L[i] L'[i] T :=
  ⟨h.length_eq, fun i hi hi' => List.forall₂_iff_get.1 h |>.2 i hi hi'⟩

omit hW hD hH in
theorem ListEq.refl {L : List Tm} (h : ∀ t ∈ L, ∃ T, HasTy S k .one [] t T) : ListEq S k L L := by
  induction L with
  | nil => exact .nil
  | cons a L ih =>
    obtain ⟨T, hT⟩ := h a (List.mem_cons_self ..)
    exact .cons ⟨T, EqTm.refl hT⟩ (ih fun t ht => h t (List.mem_cons_of_mem _ ht))

/-- The argument clause of a literal inductive type, from related parameter lists. -/
theorem argRelH_of {P : Tm} {l : ℕ} (hP : HasTy S k .one [] (.data d P) (.univ l)) (hpl : P = Tm.ofList P.toList)
    {k' : ℕ} (σ : ISub k' k) {ps ps' : Tm}
    (hpar : ∀ k'' (σ' : ISub k'' k'), ParRel2 S k'' D (ps.isub σ').toList (ps'.isub σ').toList)
    (hpeq : ∀ k'' (σ' : ISub k'' k'), ListEq S k'' (P.isub (σ.comp σ')).toList (ps.isub σ').toList) :
    argRelH (ΘK S D d k P) (Hom.id k) S k' σ.hom ps ps' := by
  intro k'' σ' c C args args' hC hl hl' hr hrec hpt
  simp only [show (ΘK S D d k P).idx = d from rfl, dataD_eq hW hD] at hC hrec hpt ⊢
  have hΛ : (ΘK S D d k P).restr ((Hom.id k).comp (σ.hom.comp σ'.hom)) = ΘK S D d k'' (P.isub (σ.comp σ')) := by
    rw [Hom.id_comp, ← ISub.hom_comp]; exact ΘK_restr P (σ.comp σ')
  simp only [dataP2] at hpt
  rw [hΛ] at hpt
  rw [hΛ]
  have hPτ : HasTy S k'' .one [] (.data d (P.isub (σ.comp σ'))) (.univ l) := HasTy.isubS hW hP (σ.comp σ')
  have hplτ : P.isub (σ.comp σ') = Tm.ofList (P.isub (σ.comp σ')).toList := isList_subst hpl _ _
  obtain ⟨hc', hCeq⟩ := List.getElem?_eq_some_iff.1 hC
  -- typing and naturality of the arguments
  have htyA : ∀ i (hi : i < args.length) (hi' : i < args'.length), ∃ T, HasTy S k'' .one [] args[i] T := by
    intro i hi hi'
    cases hri : C.isRec i
    · exact ⟨_, (Comp2_el (hpt i hi hi' hri)).1.1⟩
    · cases hrec i hi hi' hri with
      | intro he _ _ _ => exact ⟨_, minimal_to_spec (presup hW (spec_to_minimal_eq hW he)).1⟩
  have hnat : ∀ t ∈ args, Natural S t k'' (idEnv k'') (γ0 k'') := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨T, hT⟩ := htyA i hi (by omega)
    exact natural_of_ty hW hT
  have hargsEq : ∀ j, j ≤ args.length → ListEq S k'' (args.take j) (args.take j) := fun j _ =>
    ListEq.refl fun t ht => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
      simp only [List.getElem_take]
      exact htyA i (by simp at hi; omega) (by simp at hi; omega)
  -- the codes of the point argument types
  have hcode : ∀ j (hj : j < C.args.length) (hjl : j ≤ args.length), C.isRec j = false →
      ValidPre (ΘK S D d k'' (P.isub (σ.comp σ'))) c j ((args.take j).map (semK S k'')) →
      tyLook (shapeV (ΘK S D d k'' (P.isub (σ.comp σ')))) c j ((args.take j).map (semK S k'')) =
        semK S k'' ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ (ps.isub σ').toList.reverse)) := by
    intro j hj hjl hrj hv
    obtain ⟨A, hA⟩ := point_of_not_rec hj hrj
    rw [tyLook_code hW hD hPτ hplτ hC hA (by simp; omega) (fun t ht => hnat t (List.mem_of_mem_take ht)) hv]
    have hE : ListEq S k'' ((args.take j).reverse ++ (P.isub (σ.comp σ')).toList.reverse)
        ((args.take j).reverse ++ (ps.isub σ').toList.reverse) :=
      List.rel_append (List.forall₂_reverse_iff.2 (hargsEq j hjl)) (List.forall₂_reverse_iff.2 (hpeq k'' σ'))
    exact semK_substList_congr hW _ hE.get.1 hE.get.2
  have hargs : ∀ i (hi : i < args.length) (hi' : i < args'.length), C.isRec i = false →
      RE2 S k'' ((C.argTy d D.params.length i).substList ((args.take i).reverse ++ (ps.isub σ').toList.reverse))
        args[i] args'[i] := by
    intro i hi hi' hri
    have h := hpt i hi hi' hri
    have hv := validPre2_of_el h
    unfold RE2
    rw [← hcode i (by omega) hi.le hri hv]
    exact h
  -- the valid prefix of the arguments
  have hv : ValidPre (ΘK S D d k'' (P.isub (σ.comp σ'))) c args.length (args.map (semK S k'')) := by
    refine ⟨hc', by simp only [show (ΘK S D d k'' (P.isub (σ.comp σ'))).ctors = D.ctors from rfl, hCeq]; omega,
      by simp, fun i hi => ?_⟩
    simp only [List.length_map] at hi
    simp only [argSet, show (ΘK S D d k'' (P.isub (σ.comp σ'))).ctors = D.ctors from rfl, hCeq]
    split
    · rename_i hri
      have := DR2.memL hW (hrec i hi (by omega) (by simpa using hri))
      simp only [dataMem] at this
      rw [hΛ] at this
      simpa using this
    · rename_i hri
      have hri' : C.isRec i = false := by simpa using hri
      have h := hpt i hi (by omega) hri'
      have hvi := validPre2_of_el h
      have := (Comp2_el h).2
      rw [El_res, Hom.comp_id, tyLook_eq hvi] at this
      simpa [List.map_take] using this
  have hc := hcode args.length hl (Nat.le_refl _) hr (by simpa using hv)
  simp only [List.take_length] at hc
  rw [hc]
  exact argTy_rel hW hD hH hC (hpar k'' σ') hl hl' hr hargs

end

end Model.Whnf
