import Model.Whnf.Valid2TranspGlue
import Model.Whnf.Kan2DataBasic
import Model.Whnf.Kan2DataTArgs
import Model.Whnf.Kan2DataCode

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
  pointsKan : ∀ d < n, ∀ (D : DataDecl), S[d]? = some (.data D) → ∀ (c : ℕ) (C : Ctor), D.ctors[c]? = some C →
    ∀ (i : ℕ) (A : Tm), C.args[i]? = some (.point A) →
    ∀ k (cs : CSub2 S 0 .one (D.pointCtx d C i) k),
      KanP2 S k (semK S k (cs.L (A.ren (C.pointRen i) id)))

theorem DeclHyp2.mono {n m : ℕ} (h : DeclHyp2 S n) (hm : m ≤ n) : DeclHyp2 S m :=
  ⟨fun d hd => h.params d (by omega), fun d hd => h.points d (by omega), fun d hd => h.pointsKan d (by omega)⟩

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
      ((C.argTy d D.params.length args.length).substList (args'.reverse ++ ps'.reverse)) ∧
    KanP2 S k (semK S k ((C.argTy d D.params.length args.length).substList (args.reverse ++ ps.reverse))) := by
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
  have hk := hH.pointsKan d (by omega) D hD c C hC args.length A0 hA0 k cs
  rw [hAk]
  rw [e1, e2] at this
  rw [e1] at hk
  exact ⟨this, hk⟩

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
  have h := argTy_rel hW hD hH hC (hpar k'' σ') hl hl' hr hargs
  exact ⟨h.1, (kanPG_iff hW).2 h.2⟩

omit hH in
/-- The recorded code of a parameter's type is the value of its type instantiated by the earlier
parameters. -/
theorem paramTyC_eq {X : Tm} (hxl : X = Tm.ofList X.toList) (hlen : X.toList.length = D.params.length)
    (hnat : ∀ t ∈ X.toList, Natural S t k (idEnv k) (γ0 k)) (i : ℕ) (hi : i < D.params.length) :
    paramTyC (sigUpTo S d) D.params[i] i k (sem S X k (idEnv k) (γ0 k)) =
      semK S k (D.params[i].substList (X.toList.take i).reverse) := by
  have hsyn : DataSyn d D := ((sigOK_of_wfSig _ S rfl hW).2 d D hD).1
  have hd : d ≤ S.length := (List.getElem?_eq_some_iff.1 hD).1.le
  have hσ : interp (sigUpTo S d) univC TyCode (D.params[i]) = sem S (D.params[i]) :=
    interp_congr_cst _ _ (sigUpTo_agree S S.length hd) _ (hsyn.2.1 i _ (List.getElem?_eq_getElem hi)).2
  unfold paramTyC semK
  rw [hσ, Tm.substList, sem_subst S _ k _ _ _ _ (natural_substList fun t ht =>
      hnat t (List.mem_of_mem_take (List.mem_reverse.1 ht)))]
  obtain ⟨hcl, -⟩ := hsyn.2.1 i _ (List.getElem?_eq_getElem hi)
  symm
  refine interp_congr_closed _ _ _ _ i 0 hcl k _ _ _ _ (fun _ h => absurd h (by omega)) (fun x hx => ?_)
  have hx' : x < ((X.toList.take i).reverse).length := by simp; omega
  rw [sem_substList_env _ _ _ x hx']
  simp only [argEnv, List.reverse_nil, List.append_nil, plist]
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by simp; omega)]
  simp only [List.length_map, List.length_range, List.getElem?_map, List.getElem?_range (by omega : i - 1 - x < i),
    Option.map_some, Option.getD_some]
  rw [sem_vnth X _ _ _ (by omega), List.getElem_reverse, List.getElem_take]
  congr 2; simp; omega

/-- The parameter clause of a literal inductive type, from related parameter lists. -/
theorem parRel2_of {P : Tm} {l : ℕ} (hP : HasTy S k .one [] (.data d P) (.univ l)) (hpl : P = Tm.ofList P.toList)
    {k' : ℕ} (σ : ISub k' k) {ps ps' : Tm} (hrel : ParRel2 S k' D ps.toList ps'.toList)
    (hpeq : ListEq S k' (P.isub σ).toList ps.toList) :
    parRel2 S (ΘK S D d k P) (Hom.id k) k' σ ps ps' := by
  intro j p p' hp hp'
  obtain ⟨hjps, rfl⟩ := List.getElem?_eq_some_iff.1 hp
  obtain ⟨hjps', rfl⟩ := List.getElem?_eq_some_iff.1 hp'
  have hjD : j < D.params.length := by rw [← hrel.1]; exact hjps
  have hPσ : HasTy S k' .one [] (.data d (P.isub σ)) (.univ l) := HasTy.isubS hW hP σ
  have hplσ : P.isub σ = Tm.ofList (P.isub σ).toList := isList_subst hpl _ _
  have hlenσ : (P.isub σ).toList.length = D.params.length := by rw [hpeq.get.1, hrel.1]
  have hjP : j < (P.isub σ).toList.length := by omega
  have hnat : ∀ t ∈ (P.isub σ).toList, Natural S t k' (idEnv k') (γ0 k') := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨T, e⟩ := hpeq.get.2 i hi (by rw [← hpeq.get.1]; exact hi)
    exact (natural_of_eq hW e).1
  have hent : parEntry (ΘK S D d k P) (Hom.id k) k' σ j =
      paramEntry (sigUpTo S d) D j k' (sem S (P.isub σ) k' (idEnv k') (γ0 k')) := by
    unfold parEntry
    rw [Hom.id_comp, ΘK_restr P σ]
    show vnth (vlist ((List.range D.params.length).map fun j => paramEntry (sigUpTo S d) D j k'
      (psRV S (P.isub σ) k' (idEnv k') (γ0 k') k' (Hom.id k')))) j = _
    rw [vnth_vlist_lt _ _ (by simpa using hjD)]
    simp only [List.getElem_map, List.getElem_range, psRV, IEnv.restr_id, γ0_restr]
  rw [hent]
  simp only [show (ΘK S D d k P).idx = d from rfl, dataD_eq hW hD]
  have hpe := hpeq.get.2 j hjP (by rw [← hpeq.get.1]; exact hjP)
  unfold paramEntry
  have hgen : ∀ (A : Tm), A = D.params[j] →
      (π1 (ZFSet.pair (natZ 0) (paramTyC (sigUpTo S d) A j k' (sem S (P.isub σ) k' (idEnv k') (γ0 k')))) = natZ 1 →
        (Comp2 S (π2 (ZFSet.pair (natZ 0) (paramTyC (sigUpTo S d) A j k' (sem S (P.isub σ) k' (idEnv k') (γ0 k')))))
          k' k' (Hom.id k')).ty ps.toList[j] ps'.toList[j] ∧
        KanPG S k' (Comp2 S (π2 (ZFSet.pair (natZ 0) (paramTyC (sigUpTo S d) A j k'
          (sem S (P.isub σ) k' (idEnv k') (γ0 k'))))) k')) ∧
      (π1 (ZFSet.pair (natZ 0) (paramTyC (sigUpTo S d) A j k' (sem S (P.isub σ) k' (idEnv k') (γ0 k')))) = natZ 0 →
        ∀ Aj, D.params[j]? = some Aj →
        (Comp2 S (π2 (ZFSet.pair (natZ 0) (paramTyC (sigUpTo S d) A j k' (sem S (P.isub σ) k' (idEnv k') (γ0 k')))))
          k' k' (Hom.id k')).ty (Aj.substList (ps.toList.take j).reverse) (Aj.substList (ps'.toList.take j).reverse) ∧
        (Comp2 S (π2 (ZFSet.pair (natZ 0) (paramTyC (sigUpTo S d) A j k' (sem S (P.isub σ) k' (idEnv k') (γ0 k')))))
          k' k' (Hom.id k')).el (Aj.substList (ps.toList.take j).reverse) ps.toList[j] ps'.toList[j]) := by
    rintro A rfl
    simp only [π1_pair, π2_pair]
    refine ⟨fun h => absurd h (by intro h; exact absurd (natZ_inj.1 h) (by decide)), fun _ Aj hAj => ?_⟩
    rw [List.getElem?_eq_getElem hjD] at hAj
    cases hAj
    rw [paramTyC_eq hW hD hplσ hlenσ hnat j hjD]
    have hc : semK S k' (D.params[j].substList ((P.isub σ).toList.take j).reverse) =
        semK S k' (D.params[j].substList (ps.toList.take j).reverse) := by
      have hE := List.forall₂_reverse_iff.2 (List.forall₂_take j hpeq)
      exact semK_substList_congr hW _ (ListEq.get hE).1 (ListEq.get hE).2
    rw [hc]
    exact ⟨hrel.ty hW hD hH j hjD, hrel.2.2 j hjps hjps' hjD⟩
  split
  · rename_i kk heq
    have heq' : D.params[j] = .univ kk := by rw [List.getElem?_eq_getElem hjD] at heq; injection heq
    split
    · simp only [π1_pair, π2_pair]
      refine ⟨fun _ => ?_, fun h => absurd (natZ_inj.1 h) (by decide)⟩
      rw [sem_vnth _ _ _ j hjP]
      obtain ⟨T, e⟩ := hpe
      change (Comp2 S (semK S k' _) k' k' (Hom.id k')).ty _ _ ∧
        KanPG S k' (Comp2 S (semK S k' _) k')
      rw [semK_eq hW e]
      have h := hrel.2.2 j hjps hjps' hjD
      rw [heq'] at h
      exact ⟨RE2_univ_ty hW h, (kanPG_iff hW).2 (RE2_univ_kan hW h)⟩
    · exact hgen _ heq'.symm
  · rename_i A _ heq
    have heq' : D.params[j] = A := by rw [List.getElem?_eq_getElem hjD] at heq; injection heq
    exact hgen _ heq'.symm
  · rename_i heq; rw [List.getElem?_eq_getElem hjD] at heq; cases heq

omit hW hD hH in
theorem paramEntry_point {σv : SigV} {j n : ℕ} {psv : V} {A : Tm} (hA : D.params[j]? = some A)
    (hu : ¬ ∃ kk, A = .univ kk ∧ kk ≤ D.level) :
    paramEntry σv D j n psv = ZFSet.pair (natZ 0) (paramTyC σv A j n psv) := by
  unfold paramEntry
  rw [hA]
  cases A with
  | univ kk => simp only [show ¬ kk ≤ D.level from fun h => hu ⟨kk, rfl, h⟩, if_false]
  | _ => rfl

omit hH in
/-- The parameter clause of a literal inductive type, back to related parameters. -/
theorem parRel2_inv {P : Tm} {l : ℕ} (hP : HasTy S k .one [] (.data d P) (.univ l)) (hpl : P = Tm.ofList P.toList)
    {k' : ℕ} (σ : ISub k' k) {ps' : Tm} (h : parRel2 S (ΘK S D d k P) (Hom.id k) k' σ (P.isub σ) ps')
    (hty : ∀ t ∈ (P.isub σ).toList, ∃ T, HasTy S k' .one [] t T)
    {j : ℕ} {p p' A : Tm} (hp : (P.isub σ).toList[j]? = some p) (hp' : ps'.toList[j]? = some p')
    (hA : D.params[j]? = some A)
    (he : ∀ kk, A = .univ kk → EqTm S k' .one [] p p' (.univ kk)) :
    RE2 S k' (A.substList ((P.isub σ).toList.take j).reverse) p p' := by
  have hjD : j < D.params.length := (List.getElem?_eq_some_iff.1 hA).1
  have hAj : D.params[j] = A := by rw [List.getElem?_eq_getElem hjD] at hA; exact Option.some.inj hA
  have hPσ : HasTy S k' .one [] (.data d (P.isub σ)) (.univ l) := HasTy.isubS hW hP σ
  have hplσ : P.isub σ = Tm.ofList (P.isub σ).toList := isList_subst hpl _ _
  have hlenσ : (P.isub σ).toList.length = D.params.length := by
    have := data_len_of hW (⟨l, .inl hPσ⟩ : IsTyK S k' _); rwa [dataD_eq hW hD] at this
  have hjP : j < (P.isub σ).toList.length := by omega
  have hnat : ∀ t ∈ (P.isub σ).toList, Natural S t k' (idEnv k') (γ0 k') := fun t ht => by
    obtain ⟨T, hT⟩ := hty t ht; exact natural_of_ty hW hT
  have hent : parEntry (ΘK S D d k P) (Hom.id k) k' σ j =
      paramEntry (sigUpTo S d) D j k' (sem S (P.isub σ) k' (idEnv k') (γ0 k')) := by
    unfold parEntry
    rw [Hom.id_comp, ΘK_restr P σ]
    show vnth (vlist ((List.range D.params.length).map fun j => paramEntry (sigUpTo S d) D j k'
      (psRV S (P.isub σ) k' (idEnv k') (γ0 k') k' (Hom.id k')))) j = _
    rw [vnth_vlist_lt _ _ (by simpa using hjD)]
    simp only [List.getElem_map, List.getElem_range, psRV, IEnv.restr_id, γ0_restr]
  have H := h j p p' hp hp'
  rw [hent] at H
  simp only [show (ΘK S D d k P).idx = d from rfl, dataD_eq hW hD] at H
  have ep : (P.isub σ).toList[j] = p := (List.getElem?_eq_some_iff.1 hp).2
  by_cases hu : ∃ kk, A = .univ kk ∧ kk ≤ D.level
  · obtain ⟨kk, rfl, hkk⟩ := hu
    have e : paramEntry (sigUpTo S d) D j k' (sem S (P.isub σ) k' (idEnv k') (γ0 k')) =
        ZFSet.pair (natZ 1) (vnth (sem S (P.isub σ) k' (idEnv k') (γ0 k')) j) := by
      unfold paramEntry; rw [hA]; simp only [hkk, if_true]
    rw [e] at H
    simp only [π1_pair, π2_pair] at H
    have hrt := H.1 trivial
    rw [sem_vnth _ _ _ j hjP, ep] at hrt
    show RE2 S k' (.univ kk) _ _
    have he' := he kk rfl
    exact RE2_univ_of hW ⟨HasTy.eqL he', HasTy.eqR he', he'⟩ hrt.1 ((kanPG_iff hW).1 hrt.2)
  · rw [paramEntry_point hA hu] at H
    simp only [π1_pair, π2_pair] at H
    have H2 := (H.2 trivial A hA).2
    rw [← hAj, paramTyC_eq hW hD hplσ hlenσ hnat j hjD] at H2
    rw [← hAj]
    exact H2

omit hH in
/-- Related literal inductive types have parameter clauses at every restriction. -/
theorem parRel2_of_RT2 {P Q : Tm} {l : ℕ} (hP : HasTy S k .one [] (.data d P) (.univ l))
    (h : RT2 S k (.data d P) (.data d Q)) {k' : ℕ} (σ : ISub k' k) :
    parRel2 S (ΘK S D d k P) (Hom.id k) k' σ (P.isub σ) (Q.isub σ) := by
  unfold RT2 at h
  rw [semK_dataT hW hD hP, Comp2_dataC] at h
  obtain ⟨ps1, ps2, h1, h2, -, -, -, -, -, -, hpar⟩ := h.2.1 k' σ
  obtain rfl := redT_data_eq (Θ := ΘK S D d k P) h1
  obtain rfl := redT_data_eq (Θ := ΘK S D d k P) h2
  exact hpar

omit hD hH in
theorem ListEq.of_parRel2 {ps ps' : List Tm} (h : ParRel2 S k D ps ps') :
    ListEq S k ps ps ∧ ListEq S k ps ps' := by
  have hl : ps.length = ps'.length := by rw [h.1, h.2.1]
  refine ⟨ListEq.refl fun t ht => ?_, List.forall₂_iff_get.2 ⟨hl, fun i hi hi' => ?_⟩⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    exact ⟨_, (RE2.typed (h.2.2 i hi (by omega) (by rw [← h.1]; exact hi))).1⟩
  · exact ⟨_, (RE2.typed (h.2.2 i hi hi' (by rw [← h.1]; exact hi))).2.2⟩

/-- **Literal inductive types at related parameters are related.** -/
theorem RT2_dataLit {P Q : Tm} {l : ℕ} (hP : HasTy S k .one [] (.data d P) (.univ l))
    (hQ : HasTy S k .one [] (.data d Q) (.univ l)) (hPQ : TyEq S k (.data d P) (.data d Q))
    (hpl : P = Tm.ofList P.toList) (hql : Q = Tm.ofList Q.toList)
    (hrel : ∀ k' (σ : ISub k' k), ParRel2 S k' D (P.isub σ).toList (Q.isub σ).toList) :
    RT2 S k (.data d P) (.data d Q) := by
  have hr2 : ∀ k' (σ : ISub k' k) k'' (σ' : ISub k'' k') (X : Tm),
      ((X.isub σ).isub σ').toList = (X.isub (σ.comp σ')).toList := fun _ σ _ σ' X => by rw [Tm.isub_isub]
  have hPP : ∀ k' (σ : ISub k' k) k'' (σ' : ISub k'' k'),
      ListEq S k'' (P.isub (σ.comp σ')).toList ((P.isub σ).isub σ').toList := fun k' σ k'' σ' => by
    rw [hr2]; exact (ListEq.of_parRel2 hW (hrel k'' (σ.comp σ'))).1
  have hPQl : ∀ k' (σ : ISub k' k) k'' (σ' : ISub k'' k'),
      ListEq S k'' (P.isub (σ.comp σ')).toList ((Q.isub σ).isub σ').toList := fun k' σ k'' σ' => by
    rw [hr2]; exact (ListEq.of_parRel2 hW (hrel k'' (σ.comp σ'))).2
  have hrel' : ∀ k' (σ : ISub k' k) k'' (σ' : ISub k'' k'),
      ParRel2 S k'' D ((P.isub σ).isub σ').toList ((Q.isub σ).isub σ').toList := fun k' σ k'' σ' => by
    rw [hr2, hr2]; exact hrel k'' (σ.comp σ')
  have hsemQ : semK S k (.data d Q) = semK S k (.data d P) := (semK_tyEq hW hPQ).symm
  unfold RT2
  rw [semK_dataT hW hD hP, Comp2_dataC]
  simp only [show (ΘK S D d k P).idx = d from rfl]
  have hTP : IsTyK S k (.data d P) := ⟨l, .inl hP⟩
  have hTQ : IsTyK S k (.data d Q) := ⟨l, .inl hQ⟩
  refine ⟨⟨hTP, hTQ, ?_, ?_, hPQ⟩, fun k' σ => ?_, ?_, ?_⟩
  · rw [← semK_dataT hW hD hP, res_id (kv_semK_of_univ hW hP)]
  · rw [hsemQ, ← semK_dataT hW hD hP, res_id (kv_semK_of_univ hW hP)]
  · refine ⟨P.isub σ, Q.isub σ, ⟨redW_self (step_data d _), TyEq.refl _⟩, ⟨redW_self (step_data d _), TyEq.refl _⟩,
      isList_subst hpl _ _, isList_subst hql _ _, ?_, ?_, ?_, ?_, ?_⟩
    · exact (argRel2_iff _ σ).2 (argRelH_of hW hD hH hP hpl σ (hrel' k' σ) (hPP k' σ))
    · exact (argRel2_iff _ σ).2 (argRelH_of hW hD hH hP hpl σ (fun k'' σ' => (hrel' k' σ k'' σ').symm hW hD hH)
        (hPQl k' σ))
    · exact (argRel2_iff _ σ).2 (argRelH_of hW hD hH hP hpl σ (fun k'' σ' => (hrel' k' σ k'' σ').left hW hD hH)
        (hPP k' σ))
    · exact (argRel2_iff _ σ).2 (argRelH_of hW hD hH hP hpl σ (fun k'' σ' => (hrel' k' σ k'' σ').right hW hD hH)
        (hPQl k' σ))
    · exact parRel2_of hW hD hH hP hpl σ (hrel k' σ) (ListEq.of_parRel2 hW (hrel k' σ)).1
  · intro k' σ k'' σ' ps1 ps2 h1 h2
    obtain rfl := redT_data_eq (Θ := ΘK S D d k P) h1
    obtain rfl := redT_data_eq (Θ := ΘK S D d k P) h2
    rw [show (Tm.subst Tm.var σ.τ P).isub σ' = P.isub (σ.comp σ') from Tm.isub_isub P σ σ']
    have hs := fun k3 (σ3 : ISub k3 k'') => hrel' k'' (σ.comp σ') k3 σ3
    refine ⟨(argRel2_iff _ _).2 (argRelH_of hW hD hH hP hpl (σ.comp σ') (fun k3 σ3 => (hs k3 σ3).left hW hD hH)
        (hPP k'' (σ.comp σ'))), (argRel2_iff _ _).2 (argRelH_of hW hD hH hP hpl (σ.comp σ')
        (fun k3 σ3 => (hs k3 σ3).left hW hD hH) (hPP k'' (σ.comp σ'))), ?_⟩
    exact parRel2_of hW hD hH hP hpl (σ.comp σ') ((hrel k'' (σ.comp σ')).left hW hD hH)
      (ListEq.of_parRel2 hW (hrel k'' (σ.comp σ'))).1
  · intro k' σ k'' σ' ps1 ps2 h1 h2
    obtain rfl := redT_data_eq (Θ := ΘK S D d k P) h1
    obtain rfl := redT_data_eq (Θ := ΘK S D d k P) h2
    rw [show (Tm.subst Tm.var σ.τ Q).isub σ' = Q.isub (σ.comp σ') from Tm.isub_isub Q σ σ']
    have hs := fun k3 (σ3 : ISub k3 k'') => hrel' k'' (σ.comp σ') k3 σ3
    refine ⟨(argRel2_iff _ _).2 (argRelH_of hW hD hH hP hpl (σ.comp σ') (fun k3 σ3 => (hs k3 σ3).right hW hD hH)
        (hPQl k'' (σ.comp σ'))), (argRel2_iff _ _).2 (argRelH_of hW hD hH hP hpl (σ.comp σ')
        (fun k3 σ3 => (hs k3 σ3).right hW hD hH) (hPQl k'' (σ.comp σ'))), ?_⟩
    exact parRel2_of hW hD hH hP hpl (σ.comp σ') ((hrel k'' (σ.comp σ')).right hW hD hH)
      (ListEq.of_parRel2 hW (hrel k'' (σ.comp σ'))).2

/-! ### Formation -/

omit hW hD hH in
theorem VTele2.get {Ψ : ℕ} {Φ : I} {Γ : Ctx} : ∀ {ts ts' : Tm} {Δ prev : List Tm}, VTele2 S Ψ Φ Γ ts ts' Δ prev →
    ∀ j (hj : j < ts.toList.length) (hj' : j < ts'.toList.length) (hΔ : j < Δ.length),
      Valid2 S Ψ Φ Γ ts.toList[j] ts'.toList[j] (Δ[j].substList ((ts.toList.take j).reverse ++ prev))
  | .tcons a as, .tcons a' as', A :: Δ, prev, ⟨h1, h2⟩ => fun j hj hj' hΔ => by
    cases j with
    | zero => simpa [Tm.toList] using h1
    | succ j =>
      have := VTele2.get h2 j (by simp [Tm.toList] at hj; omega) (by simp [Tm.toList] at hj'; omega)
        (by simp at hΔ; omega)
      simpa [Tm.toList, List.take_succ_cons, List.reverse_cons, List.append_assoc] using this
  | .tnil, _, [], _, _ => fun j hj => by simp [Tm.toList] at hj
  | .tnil, .tnil, _ :: _, _, h => h.elim
  | .tnil, .tcons _ _, _, _, h => by cases h
  | .tcons _ _, .tnil, _, _, h => by cases h
  | .tcons _ _, .tcons _ _, [], _, h => h.elim

omit hD hH in
/-- The left elements of related telescopes are related to themselves. -/
theorem VTele2.left {Ψ : ℕ} {Φ : I} {Γ : Ctx} : ∀ {ts ts' : Tm} {Δ prev : List Tm}, VTele2 S Ψ Φ Γ ts ts' Δ prev →
    VTele2 S Ψ Φ Γ ts ts Δ prev
  | .tnil, .tnil, [], _, _ => trivial
  | .tcons _ _, .tcons _ _, _ :: _, _, ⟨h1, h2⟩ => ⟨valid_trans hW h1 (valid_symm hW h1), VTele2.left h2⟩
  | .tnil, .tnil, _ :: _, _, h => h.elim
  | .tnil, .tcons _ _, _, _, h => by cases h
  | .tcons _ _, .tnil, _, _, h => by cases h
  | .tcons _ _, .tcons _ _, [], _, h => h.elim

omit hW hD hH in
/-- Related telescopes from related components. -/
theorem VTele2.ofList {Ψ : ℕ} {Φ : I} {Γ : Ctx} : ∀ (L L' Δ prev : List Tm), L.length = Δ.length → L'.length = Δ.length →
    (∀ j (hj : j < L.length) (hj' : j < L'.length) (hΔ : j < Δ.length),
      Valid2 S Ψ Φ Γ L[j] L'[j] (Δ[j].substList ((L.take j).reverse ++ prev))) →
    VTele2 S Ψ Φ Γ (Tm.ofList L) (Tm.ofList L') Δ prev
  | [], [], [], _, _, _, _ => trivial
  | a :: L, a' :: L', A :: Δ, prev, hl, hl', h =>
    ⟨by simpa using h 0 (by simp) (by simp) (by simp),
      VTele2.ofList L L' Δ (a :: prev) (by simpa using hl) (by simpa using hl') fun j hj hj' hΔ => by
        simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using
          h (j + 1) (by simp; omega) (by simp; omega) (by simp; omega)⟩
  | [], [], _ :: _, _, hl, _, _ => by simp at hl
  | [], _ :: _, _, _, hl, hl', _ => by simp at hl hl'; omega
  | _ :: _, [], _, _, hl, hl', _ => by simp at hl hl'; omega
  | _ :: _, _ :: _, [], _, hl, _, _ => by simp at hl

omit hW hD hH in
theorem VTele2.shape {Ψ : ℕ} {Φ : I} {Γ : Ctx} : ∀ {ts ts' : Tm} {Δ prev : List Tm}, VTele2 S Ψ Φ Γ ts ts' Δ prev →
    ts = Tm.ofList ts.toList ∧ ts' = Tm.ofList ts'.toList ∧ ts.toList.length = Δ.length ∧ ts'.toList.length = Δ.length
  | .tnil, .tnil, [], _, _ => ⟨rfl, rfl, rfl, rfl⟩
  | .tcons a as, .tcons a' as', A :: Δ, prev, ⟨_, h2⟩ => by
    obtain ⟨e1, e2, l1, l2⟩ := VTele2.shape h2
    refine ⟨?_, ?_, ?_, ?_⟩
    · show Tm.tcons a as = Tm.tcons a (Tm.ofList as.toList); rw [← e1]
    · show Tm.tcons a' as' = Tm.tcons a' (Tm.ofList as'.toList); rw [← e2]
    · simp [Tm.toList, l1]
    · simp [Tm.toList, l2]
  | .tnil, .tnil, _ :: _, _, h => h.elim
  | .tnil, .tcons _ _, _, _, h => by cases h
  | .tcons _ _, .tnil, _, _, h => by cases h
  | .tcons _ _, .tcons _ _, [], _, h => h.elim

/-- Valid parameters instantiate to related parameter lists. -/
theorem parRel2_of_vtele {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ps ps' : Tm}
    (hv : VTele2 S Ψ Φ Γ ps ps' D.params []) (c : CSub2 S Ψ Φ Γ k) :
    ParRel2 S k D (c.L ps).toList (c.R ps').toList := by
  obtain ⟨hpl, hpl', hlen, hlen'⟩ := VTele2.shape hv
  have e1 : (c.L ps).toList = ps.toList.map c.L := toList_subst hpl _ _
  have e2 : (c.R ps').toList = ps'.toList.map c.R := toList_subst hpl' _ _
  refine ⟨by rw [e1]; simpa using hlen, by rw [e2]; simpa using hlen', fun j hj hj' hjD => ?_⟩
  have hj0 : j < ps.toList.length := by rw [e1] at hj; simpa using hj
  have hj0' : j < ps'.toList.length := by rw [e2] at hj'; simpa using hj'
  have h := (VTele2.get hv j hj0 hj0' hjD k c).2
  have hcl : (D.params[j]).closedB (((ps.toList.take j).reverse ++ [])).length 0 = true := by
    have := params_closed (sigClosed_of_wfSig hW) hD j _ (List.getElem?_eq_getElem hjD)
    simpa [Nat.min_eq_left hj0.le] using this
  have e3 : c.L ((D.params[j]).substList ((ps.toList.take j).reverse ++ [])) =
      (D.params[j]).substList ((c.L ps).toList.take j).reverse := by
    show ((D.params[j]).substList _).subst c.γ c.σ.τ = _
    rw [substList_subst hcl, e1, List.append_nil, List.map_reverse, List.map_take]
  rw [e3, e1] at h
  simp only [e1, e2, List.getElem_map]
  exact h

/-- **Formation**: a data type at valid parameters is valid. -/
theorem valid_data (hHit : HITHyp2 S (d + 1)) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ps : Tm} (hlev : D.level + 1 ≤ maxLevel)
    (ht : HasTele0 S Ψ Φ Γ ps D.params []) (hv : VTele2 S Ψ Φ Γ ps ps D.params []) :
    Valid2 S Ψ Φ Γ (.data d ps) (.data d ps) (.univ D.level) := by
  have hty := HasTy0.data hD hlev ht
  have hpl := tele_isList ht
  refine valid_univ_of hW hty hty (.refl hty) (fun k c => ?_) (fun k c => by
    change KanP2 S k (semK S k (.data d (c.L ps)))
    rw [semK_dataT hW hD (c.ty hW hty)]
    exact kanP2_dataC hW hD hHit)
  refine RT2_dataLit hW hD hH (P := c.L ps) (Q := c.R ps) (c.ty hW hty) (c.tyR' hW hty)
    (.inr ⟨_, c.eqLR hW hty⟩) (isList_subst hpl _ _) (isList_subst hpl _ _) fun k' σ => ?_
  rw [← CSub2.restr_L hW c σ ps, ← CSub2.restr_R hW c σ ps]
  exact parRel2_of_vtele hW hD hH hv (c.restr hW σ)

/-- Congruence of formation. -/
theorem valid_dataEq (hHit : HITHyp2 S (d + 1)) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ps ps' : Tm}
    (hty : HasTy0 S Ψ Φ Γ (.data d ps) (.univ D.level)) (hty' : HasTy0 S Ψ Φ Γ (.data d ps') (.univ D.level))
    (heq : EqTm0 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ D.level)) (hv : VTele2 S Ψ Φ Γ ps ps' D.params []) :
    Valid2 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ D.level) := by
  obtain ⟨hpl, hpl', -, -⟩ := VTele2.shape hv
  refine valid_univ_of hW hty hty' heq (fun k c => ?_) (fun k c => by
    change KanP2 S k (semK S k (.data d (c.L ps)))
    rw [semK_dataT hW hD (c.ty hW hty)]
    exact kanP2_dataC hW hD hHit)
  refine RT2_dataLit hW hD hH (P := c.L ps) (Q := c.R ps') (c.ty hW hty) (c.tyR' hW hty')
    (.inr ⟨_, c.eq hW heq⟩) (isList_subst hpl _ _) (isList_subst hpl' _ _) fun k' σ => ?_
  rw [← CSub2.restr_L hW c σ ps, ← CSub2.restr_R hW c σ ps']
  exact parRel2_of_vtele hW hD hH hv (c.restr hW σ)

/-! ### Constructors -/

omit hH in
theorem argTy_closed {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) (j : ℕ) :
    (C.argTy d D.params.length j).closedB (D.params.length + j) 0 = true := by
  have hsyn : DataSyn d D := ((sigOK_of_wfSig _ S rfl hW).2 d D hD).1
  unfold Ctor.argTy; split
  · rename_i A hA
    exact (hsyn.2.2.1 c C hC j A hA).1
  · show (Tm.data d _).closedB _ 0 = true
    simp only [Tm.closedB]; exact paramVars_closed _ _

/-- **Constructors** of an inductive type without path constructors, at valid parameters and arguments. -/
theorem valid_con_nonHIT (hHIT : D.isHIT = false) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {c : ℕ} {C : Ctor} {ps ps' args args' : Tm}
    {rs rs' : List I} (hC : D.ctors[c]? = some C) (hpl : ps = Tm.ofList ps.toList)
    (hcon : HasTy0 S Ψ Φ Γ (.con d c ps args rs) (.data d ps))
    (heq : EqTm0 S Ψ Φ Γ (.con d c ps args rs) (.con d c ps' args' rs') (.data d ps))
    (hpsl : ps.toList.length = D.params.length) (hal : args = Tm.ofList args.toList)
    (hal' : args' = Tm.ofList args'.toList) (hall : args.toList.length = C.args.length)
    (hall' : args'.toList.length = C.args.length) (hrs : rs.length = C.dims) (hrs' : rs'.length = C.dims)
    (hvd : Valid2 S Ψ Φ Γ (.data d ps) (.data d ps) (.univ D.level))
    (hva : VTele2 S Ψ Φ Γ args args' (C.argTys d D.params.length) ps.toList.reverse) :
    Valid2 S Ψ Φ Γ (.con d c ps args rs) (.con d c ps' args' rs') (.data d ps) := by
  have hrs0 : rs = [] := List.eq_nil_of_length_eq_zero (by rw [hrs]; exact dims_of_not_hit hHIT hC)
  have hrs0' : rs' = [] := List.eq_nil_of_length_eq_zero (by rw [hrs']; exact dims_of_not_hit hHIT hC)
  subst hrs0 hrs0'
  intro k c'
  have hvdk := hvd k c'
  have hPT : HasTy S k .one [] (.data d (c'.L ps)) (.univ D.level) := (RE2.typed hvdk.2).1
  have hPP : RT2 S k (.data d (c'.L ps)) (.data d (c'.L ps)) := by
    have := (RE2_univ_iff hW).1 hvdk.2
    exact RT2.refl hW (tyCode_of_univ hW hPT) this.2.2
  refine ⟨?_, ?_⟩
  · have := (RE2_univ_iff hW).1 hvdk.2
    have hX : RT2 S k (.data d (c'.L ps)) (.data d (c'.R ps)) := this.2.2
    exact hX
  have hpc : (c'.L ps).closedB 0 k = true := by
    have := closed_of_ty hW hPT; simpa [Tm.closedB] using this
  have eP : (c'.L ps).isub (ISub.id k) = c'.L ps := isub_id_of_closed hpc
  have hPT' : HasTy S k .one [] (.data d ((c'.L ps).isub (ISub.id k))) (.univ D.level) := by rw [eP]; exact hPT
  have hPP' : RT2 S k (.data d ((c'.L ps).isub (ISub.id k))) (.data d ((c'.L ps).isub (ISub.id k))) := by
    rw [eP]; exact hPP
  have hY : c'.L args = Tm.ofList (args.toList.map c'.L) := by
    show args.subst c'.γ c'.σ.τ = _
    conv_lhs => rw [hal]
    exact ofList_subst _ _ _
  have hY' : c'.R args' = Tm.ofList (args'.toList.map c'.R) := by
    show args'.subst c'.γ' c'.σ'.τ = _
    conv_lhs => rw [hal']
    exact ofList_subst _ _ _
  have hcT := c'.ty hW hcon
  have he := c'.eq hW heq
  show RE2 S k (.data d (c'.L ps)) (.con d c (c'.L ps) (c'.L args) []) (.con d c (c'.R ps') (c'.R args') [])
  rw [hY, hY']
  change HasTy S k .one [] (.con d c (c'.L ps) (c'.L args) []) (.data d (c'.L ps)) at hcT
  change EqTm S k .one [] (.con d c (c'.L ps) (c'.L args) []) (.con d c (c'.R ps') (c'.R args') []) (.data d (c'.L ps)) at he
  rw [hY] at hcT
  rw [hY, hY'] at he
  have hcT' : HasTy S k .one [] (.con d c (c'.L ps) (Tm.ofList (args.toList.map c'.L)) [])
      (.data d ((c'.L ps).isub (ISub.id k))) := by rw [eP]; exact hcT
  have he' : EqTm S k .one [] (.con d c (c'.L ps) (Tm.ofList (args.toList.map c'.L)) [])
      (.con d c (c'.R ps') (Tm.ofList (args'.toList.map c'.R)) []) (.data d ((c'.L ps).isub (ISub.id k))) := by
    rw [eP]; exact he
  have key := RE2_con_args hW hD hHIT hPT hPP (ISub.id k) hC (Y := args.toList.map c'.L) (Y' := args'.toList.map c'.R)
    (by rw [List.length_map, hall]) (by rw [List.length_map, hall']) hcT' he' fun i hi => ?_
  · rwa [eP] at key
  rw [eP]
  have hi0 : i < args.toList.length := by omega
  have hi0' : i < args'.toList.length := by omega
  have h := (VTele2.get hva i hi0 hi0' (by simp [Ctor.argTys]; exact hi) k c').2
  simp only [Ctor.argTys, List.getElem_map, List.getElem_range] at h
  have hcl : (C.argTy d D.params.length i).closedB ((args.toList.take i).reverse ++ ps.toList.reverse).length 0 = true := by
    simp only [List.length_append, List.length_reverse, List.length_take, hpsl, Nat.min_eq_left hi0.le]
    rw [Nat.add_comm]; exact argTy_closed hW hD hC i
  have e3 : c'.L ((C.argTy d D.params.length i).substList ((args.toList.take i).reverse ++ ps.toList.reverse)) =
      (C.argTy d D.params.length i).substList (((args.toList.map c'.L).take i).reverse ++ (c'.L ps).toList.reverse) := by
    show ((C.argTy d D.params.length i).substList _).subst c'.γ c'.σ.τ = _
    rw [substList_subst hcl, List.map_append, List.map_reverse, List.map_reverse, List.map_take,
      ← toList_subst hpl]
  rw [e3] at h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem hi0, List.getElem?_eq_getElem hi0']
  exact h

omit hH in
/-- **Injectivity of inductive types** at a parameter (the equation of the parameters is needed where
they are types, as the relation at a universe includes it). -/
theorem valid_dataInjAt {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ps ps' : Tm} {l j : ℕ} {p p' A : Tm}
    (hpl : ps = Tm.ofList ps.toList) (hpl' : ps' = Tm.ofList ps'.toList)
    (hdeq : EqTm0 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ l))
    (hj : ps.toList[j]? = some p) (hj' : ps'.toList[j]? = some p') (hA : D.params[j]? = some A)
    (heq : ∀ kk, A = .univ kk → EqTm0 S Ψ Φ Γ p p' (.univ kk))
    (hvd : Valid2 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ l))
    (hvp : Valid2 S Ψ Φ Γ p p (A.substList (ps.toList.take j).reverse)) :
    Valid2 S Ψ Φ Γ p p' (A.substList (ps.toList.take j).reverse) := by
  intro k c
  refine ⟨(hvp k c).1, ?_⟩
  have hjD : j < D.params.length := (List.getElem?_eq_some_iff.1 hA).1
  have hjp : j < ps.toList.length := (List.getElem?_eq_some_iff.1 hj).1
  have hdT : HasTy S k .one [] (.data d (c.L ps)) (.univ l) := c.ty hW (presup hW hdeq).1
  have hpc : (c.L ps).closedB 0 k = true := by
    have := closed_of_ty hW hdT; simpa [Tm.closedB] using this
  have hpc' : (c.R ps').closedB 0 k = true := by
    have := closed_of_ty hW (c.tyR' hW (presup hW hdeq).2); simpa [Tm.closedB] using this
  have hpar := parRel2_of_RT2 hW hD hdT (hvd.ty hW c) (ISub.id k)
  rw [isub_id_of_closed hpc'] at hpar
  -- the elements of the left parameters are typed
  obtain ⟨D', hD', htele⟩ := gen_data_tele (presup hW hdeq).1 rfl
  rw [hD] at hD'; cases hD'
  have hty : ∀ t ∈ ((c.L ps).isub (ISub.id k)).toList, ∃ T, HasTy S k .one [] t T := by
    rw [isub_id_of_closed hpc]
    intro t ht
    have : (c.L ps).toList = ps.toList.map c.L := toList_subst hpl _ _
    rw [this] at ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have hiD : i < D.params.length := by
      have := Meta.tele_length htele; simp at this; omega
    exact ⟨_, c.ty hW (tele_get htele i _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hiD))⟩
  have hLj : ((c.L ps).isub (ISub.id k)).toList[j]? = some (c.L p) := by
    rw [isub_id_of_closed hpc]
    show (ps.subst _ _).toList[j]? = _
    rw [toList_subst hpl, List.getElem?_map, hj]; rfl
  have hRj : (c.R ps').toList[j]? = some (c.R p') := by
    show (ps'.subst _ _).toList[j]? = _
    rw [toList_subst hpl', List.getElem?_map, hj']; rfl
  have hcl : A.closedB ((ps.toList.take j).reverse).length 0 = true := by
    have := params_closed (sigClosed_of_wfSig hW) hD j A hA
    simpa [Nat.min_eq_left hjp.le] using this
  have e3 : c.L (A.substList (ps.toList.take j).reverse) =
      A.substList (((c.L ps).isub (ISub.id k)).toList.take j).reverse := by
    rw [isub_id_of_closed hpc]
    show (A.substList _).subst c.γ c.σ.τ = _
    rw [substList_subst hcl, List.map_reverse, List.map_take, ← toList_subst hpl]
  rw [e3]
  exact parRel2_inv hW hD hdT (isList_subst hpl _ _) (ISub.id k) hpar hty hLj hRj hA
    fun kk hk => c.eq hW (heq kk hk)

omit hH in
/-- **Injectivity of inductive types**. -/
theorem valid_dataInj {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ps ps' : Tm} {l : ℕ}
    (ht : HasTele0 S Ψ Φ Γ ps D.params []) (ht' : HasTele0 S Ψ Φ Γ ps' D.params [])
    (hdeq : EqTm0 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ l))
    (hv : VTele2 S Ψ Φ Γ ps ps D.params []) (hvd : Valid2 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ l)) :
    VTele2 S Ψ Φ Γ ps ps' D.params [] := by
  have hpl := tele_isList ht
  have hpl' := tele_isList ht'
  have hl : ps.toList.length = D.params.length := by simpa using Meta.tele_length ht
  have hl' : ps'.toList.length = D.params.length := by simpa using Meta.tele_length ht'
  have hu : ∀ (kk : ℕ) (L : List Tm), (Tm.univ kk).substList L = .univ kk := fun _ _ => rfl
  rw [hpl, hpl']
  refine VTele2.ofList _ _ _ _ hl hl' fun j hj hj' hΔ => ?_
  have hjv := VTele2.get hv j hj hj hΔ
  have hA : D.params[j]? = some D.params[j] := List.getElem?_eq_getElem hΔ
  rw [List.append_nil] at hjv ⊢
  refine valid_dataInjAt hW hD hpl hpl' hdeq (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj') hA
    (fun kk hk => ?_) hvd hjv
  have p1 := tele_get ht j _ _ (List.getElem?_eq_getElem hj) hA
  have p2 := tele_get ht' j _ _ (List.getElem?_eq_getElem hj') hA
  rw [hk, hu] at p1 p2
  have hA' : D.params[j]? = some (.univ kk) := by rw [hA, hk]
  have e := EqTm0.dataInjAt hD hpl hpl' hdeq (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj') hA'
    (by rw [hu]; exact p1) (by rw [hu]; exact p2)
  rwa [hu] at e

end

end Model.Whnf
