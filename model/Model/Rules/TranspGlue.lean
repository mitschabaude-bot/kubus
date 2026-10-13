import Model.Rules.GlueComp
import Model.GlueTransp

/-!
# The computation rule `transpGlue`

The contractum `Tm.transpGlue` denotes the Glue code's transport `gtResult`.
-/

set_option autoImplicit false

namespace Model

open KubusCore KubusCore.I.M4 Model.M4
open KubusCore.I (dnf Face faces)

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

/-- The valuation with `a` for variable 0. -/
def consA (v : ℕ → M4) : ℕ → M4
  | 0 => a
  | i + 1 => v i

theorem forall0_eval {v : ℕ → M4} (hv : ∀ i, M4.IsK3 (v i)) (φ : I) :
    (I.forall0 φ).eval v = one ↔ φ.eval (consA v) = one := by
  have hv' : ∀ i, M4.IsK3 (consA v i) := fun
    | 0 => by simp [consA, M4.IsK3]
    | i + 1 => hv i
  rw [I.forall0, eval_ofFaces, Cof.dnfVal_eq_one_K3 hv, Cof.eval_eq_one_iff_faces hv']
  constructor
  · rintro ⟨c', hc', hcl⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨hc1, hc2⟩ := List.mem_filter.1 hc
    refine ⟨c, hc1, fun l hl => ?_⟩
    have hne : l.1 ≠ 0 := by have := List.all_eq_true.1 hc2 l hl; simpa using this
    have := hcl _ (List.mem_map.2 ⟨l, hl, rfl⟩)
    obtain ⟨i, d⟩ := l
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by simp at hne; omega⟩
    simpa [Cof.LitHolds, consA] using this
  · rintro ⟨c, hc, hcl⟩
    have hne : ∀ l ∈ c, l.1 ≠ 0 := by
      intro l hl h0
      have := hcl l hl
      obtain ⟨i, d⟩ := l
      simp only at h0; subst h0
      cases d <;> simp [Cof.LitHolds, consA] at this
    refine ⟨c.map fun l => (l.1 - 1, l.2), List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, List.all_eq_true.2
      fun l hl => by simpa using hne l hl⟩, rfl⟩, fun l' hl' => ?_⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
    have := hcl l hl
    obtain ⟨i, d⟩ := l
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by have := hne _ hl; simp at this; omega⟩
    simpa [Cof.LitHolds, consA] using this

theorem face_ival_forall0 (ρ : IEnv m) (φ : I) :
    (ival ρ (I.forall0 φ)).face = Cof.forall0 (ival ρ.ext φ).face := by
  ext p
  have hv : ∀ (hp : p.IsK3), (fun n => (ρ.ext n).fn (Fin.snoc (α := fun _ => M4) p a : Pt (m + 1))) =
      consA (fun n => (ρ n).fn p) := by
    intro hp; funext n; cases n with
    | zero => simp [IEnv.ext, consA]
    | succ n => simp [IEnv.ext, consA, Fin.init_snoc]
  have hK : ∀ (hp : p.IsK3) n, M4.IsK3 ((ρ n).fn p) := fun hp n => (ρ n).defn.isK3 hp
  simp only [DM.face, Cof.forall0, Set.mem_setOf_eq, ival.fn]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, Cof.snoc_isK3 hp (by simp [M4.IsK3]), ?_⟩
    rw [hv hp]; exact (forall0_eval (hK hp) φ).1 h
  · rintro ⟨hp, -, h⟩
    refine ⟨hp, (forall0_eval (hK hp) φ).2 ?_⟩
    rw [← hv hp]; exact h

/-- Fibers of the function of a good equivalence code are good codes. -/
theorem tyCode_fiberM {T A p y : V} (hT : IsKV k T) (hA : IsKV k A) (h : TyCode k (equivM k T A))
    (hp : p ∈ El (arrowM k T A) (Hom.id k)) (hy : y ∈ El A (Hom.id k)) : TyCode k (fiberM k T A p y) := by
  have harr : IsKV k (arrowM k T A) := by unfold arrowM piC; exact isKV_mkKV _
  have hpkv : IsKV k p := (mem_piEl.1 (mem_arrowM hT hp)).1
  have hXkv : IsKV k (fiberM k T A p y) := by unfold fiberM sigmaC; exact isKV_mkKV _
  obtain ⟨l, hl, h | h⟩ := h
  swap
  · have := congrArg (codeTag k) h; simp [equivM, tSigma, tUniv] at this
  obtain ⟨hW, hV⟩ := h
  have hmem1 : ∃ z, ZFSet.pair p z ∈ dat (famV k (arrowM k T A) fun k' g p => isEquivM k' (res g T) (res g A) p)
      k (Hom.id k) := ⟨_, by rw [dat_famV]; exact mem_fnZ.2 ⟨_, hp, rfl⟩⟩
  have hV1 := Vt_below (below_sigmaC_famAt _ _ (isKV_famV _ _) _ _ hmem1) hV
  obtain ⟨-, hfam, -, -⟩ := WF.sigma_inv harr (isKV_famV _ _) hW
  have hW1 := hfam k (Hom.id k) p hp
  rw [apZ_dat_famV _ _ _ hp, res_id hT, res_id hA] at hW1 hV1
  unfold isEquivM at hW1 hV1
  have hmem2 : ∃ z, ZFSet.pair y z ∈ dat (famV k A fun k' g y => isContrM k' (fiberM k' (res g T) (res g A) (res g p) y))
      k (Hom.id k) := ⟨_, by rw [dat_famV]; exact mem_fnZ.2 ⟨_, hy, rfl⟩⟩
  have hV2 := Vt_below (below_piC_famAt _ _ (isKV_famV _ _) _ _ hmem2) hV1
  obtain ⟨-, hfam2, -⟩ := WF.pi_inv hA (isKV_famV _ _) hW1
  have hW2 := hfam2 k (Hom.id k) y hy
  rw [apZ_dat_famV _ _ _ hy, res_id hT, res_id hA, res_id hpkv] at hW2 hV2
  unfold isContrM at hW2 hV2
  exact ⟨l, hl, Or.inl ⟨(WF.sigma_inv hXkv (isKV_famV _ _) hW2).1, Vt_below (below_sigmaC_dom _ _ hXkv) hV2⟩⟩

theorem ival_subst_inst0 (ρ : IEnv m) (φ s : I) :
    ival ρ (φ.subst (I.inst0 s)) = (ival ρ.ext φ).restr (Hom.endpt m (ival ρ s)) := by
  rw [ival.subst, ← ival.restr, IEnv.ext_restr_endpt]
  congr 1; funext i; cases i <;> rfl

theorem face_subst_inst0 (ρ : IEnv m) (φ s : I) :
    (ival ρ (φ.subst (I.inst0 s))).face = Cof.restr (ival ρ.ext φ).face (Hom.endpt m (ival ρ s)) := by
  rw [ival_subst_inst0, DM.face_restr]

theorem TEnv.restr_wk_lift (γ : ℕ → V) (f : Hom k m) (g : Hom n (k + 1)) :
    TEnv.restr (TEnv.restr (TEnv.restr γ f) (Hom.wk k)) g =
      TEnv.restr (TEnv.restr γ (Hom.wk m)) ((Hom.lift f).comp g) := by
  rw [TEnv.restr_restr, TEnv.restr_restr, TEnv.restr_restr, ← Hom.comp_assoc (Hom.wk m), Hom.wk_comp_lift]; rfl

/-! ### Heterogeneous filling -/

theorem fill_cond {C u u0 : Tm} {ψ : I} {ρ : IEnv m} {γ : ℕ → V}
    (hty : TyCode (m + 1) (lineV S C m ρ γ)) (hN : Natural S C (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)))
    (hu : LineTubeOK (lineV S C m ρ γ) (Hom.id (m + 1)) (ival ρ ψ).face (tubeV S u ρ γ) (sem S u0 m ρ γ))
    (hu0 : sem S u0 m ρ γ ∈ El (lineV S C m ρ γ) ((Hom.id (m + 1)).comp (Hom.endpt m (DM.zero m))))
    (hu0n : Natural S u0 m ρ γ) :
    Natural S (Tm.fill C ψ u u0) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) ∧
      sem S (Tm.fill C ψ u u0) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) =
        fillF (lineV S C m ρ γ) (Hom.id (m + 1)) (ival ρ ψ).face (tubeV S u ρ γ) (sem S u0 m ρ γ) := by
  have hfib := hty.fib
  have hψ := isCof_ival_face ρ ψ
  have hwt : (Hom.wk m).comp (tfLine m) = (Hom.wk m).comp (Hom.wk (m + 1)) := by
    simp only [tfLine, Hom.wk_comp_snoc]
  have hγt : ∀ k (g : Hom k (m + 2)), TEnv.restr (TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.wk (m + 1))) g =
      TEnv.restr (TEnv.restr γ (Hom.wk m)) ((tfLine m).comp g) := by
    intro k g
    rw [TEnv.restr_restr, TEnv.restr_restr, TEnv.restr_restr, ← Hom.comp_assoc (Hom.wk m) (tfLine m) g, hwt]; rfl
  have eL : ∀ k (g : Hom k (m + 2)),
      sem S (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) k (ρ.ext.ext.restr g)
        (TEnv.restr (TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.wk (m + 1))) g) =
        res g (res (tfLine m) (lineV S C m ρ γ)) := by
    intro k g
    have e1 : (fun i => ival (ρ.ext.ext.restr g) (Tm.bind2 (.and (.var 1) (.var 0)) i)) =
        ρ.ext.restr ((tfLine m).comp g) := by
      rw [← IEnv.restr_restr, ← bind2_and_env]; rfl
    rw [sem_dsubst, e1, hγt, hN k, res_res]
  have eL0 : lineV S (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) =
      res (tfLine m) (lineV S C m ρ γ) := by
    have := eL (m + 2) (Hom.id (m + 2))
    rwa [IEnv.restr_id, TEnv.restr_id_of_kv (γ := TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.wk (m + 1)))
      (fun x => isKV_res _ _), res_id (isKV_res _ _)] at this
  have eb : sem S u0.dshift (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) = res (Hom.wk m) (sem S u0 m ρ γ) := by
    rw [sem_dshift, hu0n]
  have et : ∀ n (h : Hom n (m + 1)) r, ((fillFace (ival ρ ψ).face).restr h).holds →
      tubeV S (.split ψ.shift.shift (u.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.neg (.var 1))
        u0.dshift.dshift) ρ.ext (TEnv.restr γ (Hom.wk m)) n h r =
      fillTube (ival ρ ψ).face (tubeV S u ρ γ) (sem S u0 m ρ γ) n h r := by
    intro n h r hh
    set env := (ρ.ext.restr h).cons r
    set γ' := TEnv.restr (TEnv.restr γ (Hom.wk m)) h
    have htt : env.tail.tail = (ρ.restr (Hom.wk m)).restr h := rfl
    have hφ2 : (ival env ψ.shift.shift).holds ↔ (Cof.restr (ival ρ ψ).face ((Hom.wk m).comp h)).holds := by
      rw [ival_shift, ival_shift, htt, IEnv.restr_restr, holds_face_restr_iff]
    have hv1 : env 1 = (lastVar m).restr h := rfl
    have h0iff : (ival env (.neg (.var 1))).holds ↔ ((Cof.eq0 (lastVar m)).restr h).holds := by
      rw [holds_ival_iff_face, face_ival_neg, ival.var, hv1, Cof.eq0_restr]
    have hγ' : γ' = TEnv.restr γ ((Hom.wk m).comp h) := TEnv.restr_restr _ _ _
    have eU : sem S u0.dshift.dshift n env γ' = res ((Hom.wk m).comp h) (sem S u0 m ρ γ) := by
      rw [sem_dshift_tail, sem_dshift_tail, htt, IEnv.restr_restr, hγ', hu0n]
    have eT : sem S (u.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) n env γ' =
        tubeV S u ρ γ n ((Hom.wk m).comp h) (DM.min ((lastVar m).restr h) r) := by
      rw [sem_dsubst, hγ']
      simp only [tubeV]
      congr 1
      funext i; cases i with
      | zero => rfl
      | succ i => simp [env, Tm.bind2, IEnv.cons, IEnv.restr, IEnv.ext, DM.restr_restr]
    simp only [tubeV]
    unfold fillTube
    by_cases h1 : (Cof.restr (ival ρ ψ).face ((Hom.wk m).comp h)).holds
    · have hover : (ival env (.neg (.var 1))).holds →
          sem S (u.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) n env γ' = sem S u0.dshift.dshift n env γ' := by
        intro h0
        rw [eT, eU, lastVar_zero_of (h0iff.1 h0), DM.min_zero_left]
        have := hu.base n _ h1
        simp only [tubeV] at this ⊢; exact this
      rw [sem_split (Or.inl (hφ2.2 h1)) (fun _ => hover), if_pos (hφ2.2 h1), if_pos h1, eT]
    · have h0 : ((Cof.eq0 (lastVar m)).restr h).holds := by
        rw [fillFace, Cof.or_restr, Cof.holds_or, Cof.restr_restr] at hh
        exact hh.resolve_left h1
      rw [sem_split (Or.inr (h0iff.2 h0)) (fun h => absurd (hφ2.1 h) h1), if_neg (fun h => h1 (hφ2.1 h)),
        if_neg h1, eU]
  have hT := fillTube_lineOK hfib hψ hu0 hu
  rw [Hom.id_comp] at hT
  have hcc := comp_cond (C := C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (ψ := .or ψ.shift (.neg (.var 0)))
    (u := .split ψ.shift.shift (u.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.neg (.var 1)) u0.dshift.dshift)
    (u0 := u0.dshift) (ρ := ρ.ext) (γ := TEnv.restr γ (Hom.wk m))
    (by rw [eL0]; exact hty.res _) (fun k g => (eL k g).trans (by rw [← eL0]))
    (by rw [eL0, face_fill, eb]; exact (hT.congr (isCof_fillFace hψ) fun n h r hh => (et n h r hh).symm).res_id)
    (by rw [eL0, eb, El_res, Hom.id_comp]; have := fill_base hfib hu0; rwa [Hom.id_comp] at this)
    hu0n.dshift (fun x => isKV_res _ _)
  refine ⟨hcc.1.natural, ?_⟩
  rw [Tm.fill, hcc.2, eL0, face_fill, eb, compF_res_id, fillF, Hom.id_comp]
  exact compF_congr et

/-! ### Terms under one more interval binder (`ins1`) -/

section ins1

variable {τ : ℕ → I} (hτ0 : τ 0 = .var 0) (hτs : ∀ i, τ (i + 1) = .var (i + 2))
include hτ0 hτs

theorem env_ins1 (ρ : IEnv m) (h : Hom n (m + 1)) (r : DM n) :
    (fun i => ival ((ρ.ext.restr h).cons r) (τ i)) = ρ.ext.restr (Hom.snoc ((Hom.wk m).comp h) r) := by
  rw [IEnv.ext_restr_snoc]
  funext i; cases i with
  | zero => rw [hτ0]; rfl
  | succ i => rw [hτs]; simp only [ival.var, IEnv.cons, IEnv.restr, IEnv.ext, DM.restr_restr]

theorem sem_ins1 {t : Tm} {ρ : IEnv m} {γ : ℕ → V} (hN : Natural S t (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)))
    (h : Hom n (m + 1)) (r : DM n) :
    sem S (t.dsubst τ) n ((ρ.ext.restr h).cons r) (TEnv.restr (TEnv.restr γ (Hom.wk m)) h) =
      res (Hom.snoc ((Hom.wk m).comp h) r) (sem S t (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) := by
  rw [sem_dsubst, env_ins1 hτ0 hτs, ← hN n, TEnv.restr_wk_snoc, TEnv.restr_restr]

theorem nat_ins1 {t : Tm} {ρ : IEnv m} {γ : ℕ → V} (hN : Natural S t (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)))
    (h : Hom n (m + 1)) (r : DM n) :
    Natural S (t.dsubst τ) n ((ρ.ext.restr h).cons r) (TEnv.restr (TEnv.restr γ (Hom.wk m)) h) := by
  intro k g
  rw [IEnv.cons_restr, IEnv.restr_restr, TEnv.restr_restr, sem_ins1 hτ0 hτs hN, sem_ins1 hτ0 hτs hN, res_res,
    Hom.snoc_comp, Hom.comp_assoc]

end ins1

/-! ### The data of a Glue line at a point -/

section tg

variable {A T e u0 : Tm} {φ ψ : I}

/-- The Glue face of the line. -/
abbrev tgφ (ρ : IEnv m) (φ : I) : Cof (m + 1) := (ival ρ.ext φ).face

/-- The partial `T` and `e` of the line. -/
abbrev tgP (S : Sig) (t : Tm) (φ : I) (ρ : IEnv m) (γ : ℕ → V) : V :=
  partialKV (m + 1) (tgφ ρ φ) (faceVals S t ρ.ext (TEnv.restr γ (Hom.wk m)))

/-- The hypotheses of `transpGlue` at a point. -/
structure TGCond (S : Sig) (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : Prop where
  kv : ∀ x, IsKV m (γ x)
  tr : TranspCond S (.glue A φ T e) ψ u0 m ρ γ
  Aty : TyCode (m + 1) (lineV S A m ρ γ)
  Anat : Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))
  he : ∀ k (f : Hom k (m + 1)), (Cof.restr (tgφ ρ φ) f).holds →
    sem S e k (ρ.ext.restr f) (TEnv.restr (TEnv.restr γ (Hom.wk m)) f) ∈
      El (sem S (Tm.equiv T A) k (ρ.ext.restr f) (TEnv.restr (TEnv.restr γ (Hom.wk m)) f)) (Hom.id k) ∧
    TyOK S (Tm.equiv T A) k (ρ.ext.restr f) (TEnv.restr (TEnv.restr γ (Hom.wk m)) f)

theorem tgφ_restr (ρ : IEnv m) (φ : I) (f : Hom k m) : tgφ (ρ.restr f) φ = Cof.restr (tgφ ρ φ) (Hom.lift f) := by
  show (ival (ρ.restr f).ext φ).face = _
  rw [← IEnv.ext_restr_lift, face_ival_restr]

theorem tgP_restr (t : Tm) (φ : I) (ρ : IEnv m) (γ : ℕ → V) (f : Hom k m) :
    tgP S t φ (ρ.restr f) (TEnv.restr γ f) = res (Hom.lift f) (tgP S t φ ρ γ) := by
  rw [res_partialKV, ← tgφ_restr]
  show partialKV (k + 1) (tgφ (ρ.restr f) φ) _ = _
  congr 1; funext n g
  simp only [faceVals]
  rw [← IEnv.ext_restr_lift, IEnv.restr_restr, TEnv.restr_wk_lift]

namespace TGCond

variable {ρ : IEnv m} {γ : ℕ → V} (h : TGCond S A φ T e ψ u0 m ρ γ)
include h

theorem fn : FaceNat S T φ (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) ∧
    FaceNat S e φ (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) :=
  cond_of_sem_glue (A := A) fun h0 => by
    have := h.tr.1.fib.kv; rw [lineV, h0] at this; exact not_isKV_empty this

theorem line : lineV S (.glue A φ T e) m ρ γ =
    glueC (m + 1) (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ) :=
  sem_glue h.fn.1 h.fn.2

theorem G : GlueOK (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ) :=
  glueOK_at h.fn.1 h.fn.2 h.Aty h.Anat h.he

theorem u0mem : sem S u0 m ρ γ ∈
    El (glueC (m + 1) (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ)) (eZ m) := by
  have := h.tr.2.2.1; rwa [h.line, Hom.id_comp] at this

theorem con : ConstOn (glueC (m + 1) (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ))
    (Hom.id (m + 1)) (ival ρ ψ).face := by
  have := h.tr.2.1; rwa [h.line] at this

theorem restr (f : Hom k m) : TGCond S A φ T e ψ u0 k (ρ.restr f) (TEnv.restr γ f) where
  kv := fun x => isKV_res _ _
  tr := h.tr.restr f
  Aty := by rw [line_restr h.Anat f]; exact h.Aty.res _
  Anat := line_restr_nat h.Anat f
  he := by
    intro k' g hg
    have hg' : (Cof.restr (tgφ ρ φ) ((Hom.lift f).comp g)).holds := by
      rw [← Cof.restr_restr, ← tgφ_restr]; exact hg
    have := h.he k' _ hg'
    rwa [← IEnv.restr_restr, IEnv.ext_restr_lift, ← TEnv.restr_wk_lift] at this

end TGCond

/-! ### The base and its tube -/

namespace TGCond

variable {ρ : IEnv m} {γ : ℕ → V}

/-- The data at a restricted point are the restricted data. -/
theorem nat_u0 (h : TGCond S A φ T e ψ u0 m ρ γ) (f : Hom k m) :
    sem S u0 k (ρ.restr f) (TEnv.restr γ f) = res f (sem S u0 m ρ γ) := h.tr.2.2.2.2 k f

theorem sem_e_at (h : TGCond S A φ T e ψ u0 m ρ γ) {n : ℕ} (g : Hom n (m + 1)) (hg : (Cof.restr (tgφ ρ φ) g).holds)
    {ρ' : IEnv n} {γ' : ℕ → V} (hρ : ρ' = ρ.ext.restr g) (hγ : γ' = TEnv.restr (TEnv.restr γ (Hom.wk m)) g) :
    sem S e n ρ' γ' = dat (tgP S e φ ρ γ) n g := by
  rw [dat_partialKV_holds hg, hρ, hγ]; rfl

theorem sem_a0 (h : TGCond S A φ T e ψ u0 m ρ γ) :
    sem S (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0) m ρ γ =
      gtA0 (tgφ ρ φ) (tgP S e φ ρ γ) (sem S u0 m ρ γ) := by
  rw [sem_unglue, face_subst_inst0, ival_zero, gtA0]
  by_cases hz : (Cof.restr (tgφ ρ φ) (eZ m)).holds
  · rw [sem_dinst, ival_zero, h.sem_e_at (eZ m) hz (IEnv.ext_restr_endpt _ _).symm
      (by rw [TEnv.restr_restr, Hom.wk_comp_endpt, TEnv.restr_id_of_kv h.kv])]
  · exact ungAt_not hz _ _ _

theorem tube_eq (h : TGCond S A φ T e ψ u0 m ρ γ) (n : ℕ) (g : Hom n m) (r : DM n) :
    tubeV S (.unglue φ e u0.dshift) ρ γ n g r = gtTube (tgφ ρ φ) (tgP S e φ ρ γ) (sem S u0 m ρ γ) n g r := by
  simp only [tubeV]
  rw [sem_unglue, sem_dshift_cons, h.nat_u0, gtTube, ← IEnv.ext_restr_snoc, face_ival_restr]
  by_cases hz : (Cof.restr (tgφ ρ φ) (Hom.snoc g r)).holds
  · rw [h.sem_e_at (Hom.snoc g r) hz rfl (TEnv.restr_wk_snoc γ g r).symm]
  · exact ungAt_not hz _ _ _

theorem nat_a0 (h : TGCond S A φ T e ψ u0 m ρ γ) :
    Natural S (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0) m ρ γ := by
  intro k f
  rw [(h.restr f).sem_a0, h.sem_a0, tgφ_restr, tgP_restr, h.nat_u0, gd_A0 h.G h.u0mem]

theorem tube_ok (h : TGCond S A φ T e ψ u0 m ρ γ) :
    LineTubeOK (lineV S A m ρ γ) (Hom.id (m + 1)) (ival ρ ψ).face (tubeV S (.unglue φ e u0.dshift) ρ γ)
      (sem S (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0) m ρ γ) := by
  rw [h.sem_a0]
  exact (gt_tube_ok h.G h.u0mem h.con).congr (isCof_ival_face ρ ψ) fun n g r _ => (h.tube_eq n g r).symm

theorem a0_mem (h : TGCond S A φ T e ψ u0 m ρ γ) :
    sem S (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0) m ρ γ ∈
      El (lineV S A m ρ γ) ((Hom.id (m + 1)).comp (Hom.endpt m (DM.zero m))) := by
  rw [h.sem_a0]; exact gt_A0_mem h.G h.u0mem

theorem sem_a1' (h : TGCond S A φ T e ψ u0 m ρ γ) :
    sem S (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)) m ρ γ =
      gtA1' (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) := by
  rw [(comp_cond h.Aty h.Anat h.tube_ok h.a0_mem h.nat_a0 h.kv).2, h.sem_a0, gtA1']
  exact compF_congr fun n g r _ => h.tube_eq n g r

theorem nat_a1' (h : TGCond S A φ T e ψ u0 m ρ γ) :
    Natural S (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)) m ρ γ := by
  intro k f
  rw [(h.restr f).sem_a1', h.sem_a1', line_restr h.Anat f, tgφ_restr, tgP_restr, h.nat_u0, face_ival_restr,
    gd_A1' h.G (isCof_ival_face ρ ψ) h.u0mem h.con]

theorem a1'kv (h : TGCond S A φ T e ψ u0 m ρ γ) :
    IsKV m (gtA1' (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ)) :=
  h.G.fibA.elKV _ _ _ (gt_A1'_mem h.G (isCof_ival_face ρ ψ) h.u0mem h.con)

theorem sem_fillA (h : TGCond S A φ T e ψ u0 m ρ γ) :
    Natural S (Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0))
        (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) ∧
      sem S (Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0))
        (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) =
      gtFillA (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) := by
  obtain ⟨hn, hv⟩ := fill_cond h.Aty h.Anat h.tube_ok h.a0_mem h.nat_a0
  refine ⟨hn, ?_⟩
  rw [hv, h.sem_a0, gtFillA, fillF, fillF]
  congr 1
  funext n g r
  simp only [fillTube]
  split
  · rw [h.tube_eq]
  · rfl

theorem ext_ext_eq (ρ : IEnv m) : ρ.ext.ext = (ρ.ext.restr (Hom.wk (m + 1))).cons (lastVar (m + 1)) := by
  funext i; cases i <;> rfl

theorem face_pathFace (ρ : IEnv m) (ψ : I) :
    (ival ρ.ext (.or ψ.shift (.or (.neg (.var 0)) (.var 0)))).face = pathFace (ival ρ ψ).face := by
  rw [face_ival_or, face_ival_or, face_ival_neg, face_ival_var, ival_shift,
    show ρ.ext.tail = ρ.restr (Hom.wk m) from rfl, face_ival_restr]
  rfl

/-! ### On `δ = ∀ i. φ` -/

section δ

variable (h : TGCond S A φ T e ψ u0 m ρ γ) (hδ : (Cof.forall0 (tgφ ρ φ)).holds)
include h hδ

theorem δid : ((gtδ (tgφ ρ φ)).restr (Hom.id m)).holds := by
  rw [(gt_δ_cof (isCof_ival_face ρ.ext φ)).restr_id]; exact hδ

theorem φid : (Cof.restr (tgφ ρ φ) (Hom.id (m + 1))).holds := by
  have := (gt_δ_lift (Hom.id m)).1 (h.δid hδ); rwa [Hom.lift_id] at this

theorem Tnat : Natural S T (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) := by
  have hφ : (ival ρ.ext φ).holds := by
    have := h.φid hδ; rw [(isCof_ival_face ρ.ext φ).restr_id] at this; exact (holds_iff_face _ _).2 this
  exact h.fn.1.natural_of_holds (fun x => isKV_res _ _) hφ

theorem lineT : lineV S T m ρ γ = gtTL (tgP S T φ ρ γ) (Hom.id m) := by
  rw [gtTL, Hom.lift_id, dat_partialKV_holds (h.φid hδ), faceVals, IEnv.restr_id,
    TEnv.restr_id_of_kv (γ := TEnv.restr γ (Hom.wk m)) (fun x => isKV_res _ _)]

theorem trT : TranspCond S T ψ u0 m ρ γ := by
  have hu0kv := h.G.elKV h.u0mem
  refine ⟨?_, ?_, ?_, h.Tnat hδ, h.tr.2.2.2.2⟩
  · have := (h.he (m + 1) (Hom.id (m + 1)) (h.φid hδ)).2
    unfold TyOK at this
    rw [IEnv.restr_id, TEnv.restr_id_of_kv (γ := TEnv.restr γ (Hom.wk m)) (fun x => isKV_res _ _),
      sem_equiv (h.Tnat hδ) h.Anat] at this
    have hTkv : IsKV (m + 1) (lineV S T m ρ γ) := by rw [h.lineT hδ]; exact (gt_TL_fib h.G (h.δid hδ)).kv
    exact this.equiv_dom hTkv
  · have := gt_TL_const h.G h.con (h.δid hδ)
    rwa [(isCof_ival_face ρ ψ).restr_id, ← h.lineT hδ] at this
  · have := gt_u0_TL h.G h.u0mem (h.δid hδ)
    rwa [res_id hu0kv, ← h.lineT hδ] at this

theorem sem_t1' : sem S (.transp T ψ u0) m ρ γ = gtT1' (tgP S T φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) (Hom.id m) := by
  rw [sem_transp (h.trT hδ), gtT1', h.lineT hδ, (isCof_ival_face ρ ψ).restr_id, res_id (h.G.elKV h.u0mem)]

theorem sem_tfill : sem S (Tm.transpFill T ψ u0) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) =
    transpFillF (gtTL (tgP S T φ ρ γ) (Hom.id m)) (Hom.id (m + 1)) (Cof.restr (ival ρ ψ).face (Hom.id m))
      (res (Hom.id m) (sem S u0 m ρ γ)) := by
  rw [(transpFill_cond (h.trT hδ)).2, h.lineT hδ, (isCof_ival_face ρ ψ).restr_id, res_id (h.G.elKV h.u0mem)]

theorem nat_tfill : Natural S (Tm.transpFill T ψ u0) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) :=
  (transpFill_cond (h.trT hδ)).1.natural

theorem enat : Natural S e (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) := by
  have hφ : (ival ρ.ext φ).holds := by
    have := h.φid hδ; rw [(isCof_ival_face ρ.ext φ).restr_id] at this; exact (holds_iff_face _ _).2 this
  exact h.fn.2.natural_of_holds (fun x => isKV_res _ _) hφ

theorem sem_e_ext : sem S e (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) = dat (tgP S e φ ρ γ) (m + 1) (Hom.id (m + 1)) :=
  (h.sem_e_at (Hom.id (m + 1)) (h.φid hδ) (IEnv.restr_id _).symm
    (TEnv.restr_id_of_kv (γ := TEnv.restr γ (Hom.wk m)) (fun x => isKV_res _ _)).symm)

theorem sem_e' {τ : ℕ → I} (hτ0 : τ 0 = .var 0) (hτs : ∀ i, τ (i + 1) = .var (i + 2))
    (h' : Hom n (m + 1)) (r : DM n) :
    sem S (e.dsubst τ) n ((ρ.ext.restr h').cons r) (TEnv.restr (TEnv.restr γ (Hom.wk m)) h') =
      dat (tgP S e φ ρ γ) n (Hom.snoc ((Hom.wk m).comp h') r) := by
  rw [sem_ins1 hτ0 hτs (h.enat hδ), h.sem_e_ext hδ, h.G.ecoh _ _ (h.φid hδ), Hom.id_comp]

theorem δ_at (X : Hom k m) : ((gtδ (tgφ ρ φ)).restr X).holds := by
  have := (gt_δ_cof (isCof_ival_face ρ.ext φ)).holds_restr hδ X; exact this

theorem sem_ωbase (g : Hom k (m + 1)) :
    sem S (.app (.fst (e.dinst .zero).dshift) u0.dshift) k (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ (Hom.wk m)) g) =
      eqFun k (dat (tgP S e φ ρ γ) k (Hom.snoc ((Hom.wk m).comp g) (DM.zero k)))
        (res ((Hom.wk m).comp g) (sem S u0 m ρ γ)) := by
  have hn : Natural S u0.dshift k (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ (Hom.wk m)) g) :=
    (Natural.dshift (fun k f => h.nat_u0 f)).restr g
  have hγg : TEnv.restr (TEnv.restr γ (Hom.wk m)) g = TEnv.restr γ ((Hom.wk m).comp g) := TEnv.restr_restr _ _ _
  rw [sem_app_of_nat hn, sem_fst, sem_dshift_tail, sem_dshift_tail, IEnv.tail_restr,
    show ρ.ext.tail = ρ.restr (Hom.wk m) from rfl, IEnv.restr_restr, sem_dinst, ival_zero, hγg, h.nat_u0,
    ← IEnv.ext_restr_snoc,
    h.sem_e_at (Hom.snoc ((Hom.wk m).comp g) (DM.zero k)) (gt_δ_snoc (isCof_ival_face ρ.ext φ) (h.δ_at hδ _) _) rfl
      (TEnv.restr_wk_snoc _ _ _).symm]
  rfl

theorem ωbase_id :
    sem S (.app (.fst (e.dinst .zero).dshift) u0.dshift) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) =
      gtΩBase (tgP S e φ ρ γ) (sem S u0 m ρ γ) (Hom.id m) := by
  have := h.sem_ωbase hδ (Hom.id (m + 1))
  rw [IEnv.restr_id, TEnv.restr_id_of_kv (γ := TEnv.restr γ (Hom.wk m)) (fun x => isKV_res _ _),
    Hom.comp_id] at this
  rw [this, gtΩBase, Hom.id_comp]

theorem nat_ωbase :
    Natural S (.app (.fst (e.dinst .zero).dshift) u0.dshift) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) := by
  intro k g
  have hw := h.δ_at hδ (Hom.wk m)
  have hP := gt_δ_snoc (isCof_ival_face ρ.ext φ) hw (DM.zero (m + 1))
  have hx := gt_u0_T0 h.G h.u0mem hw
  rw [h.sem_ωbase hδ g, h.ωbase_id hδ, gtΩBase, Hom.id_comp, gt_e_res h.G hP hx, Hom.snoc_comp, DM.zero_restr,
    res_res]

theorem sysω_eq {τ : ℕ → I} (hτ0 : τ 0 = .var 0) (hτs : ∀ i, τ (i + 1) = .var (i + 2))
    (n : ℕ) (h' : Hom n (m + 1)) (r : DM n) (hh : ((pathFace (ival ρ ψ).face).restr h').holds) :
    tubeV S (.split ψ.shift.shift (.app (.fst (e.dsubst τ)) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
      (.split (.neg (.var 1)) (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) (.var 1)
        ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)))
      ρ.ext (TEnv.restr γ (Hom.wk m)) n h' r =
    gtΩTube (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ)
      (Hom.id m) n h' r := by
  have hψ := isCof_ival_face ρ ψ
  simp only [tubeV]
  set E := (ρ.ext.restr h').cons r with hE
  set γ' := TEnv.restr (TEnv.restr γ (Hom.wk m)) h' with hγ'def
  set X := (Hom.wk m).comp h' with hX
  have hγ' : γ' = TEnv.restr γ X := TEnv.restr_restr _ _ _
  have htt : E.tail.tail = ρ.restr X := by
    show (ρ.restr (Hom.wk m)).restr h' = _; rw [IEnv.restr_restr]
  have hψ2 : (ival E ψ.shift.shift).holds ↔ (Cof.restr (ival ρ ψ).face X).holds := by
    rw [ival_shift, ival_shift, htt, holds_face_restr_iff]
  have hv1 : E 1 = (lastVar m).restr h' := rfl
  have hj0 : (ival E (.neg (.var 1))).holds ↔ ((Cof.eq0 (lastVar m)).restr h').holds := by
    rw [holds_ival_iff_face, face_ival_neg, ival.var, hv1, Cof.eq0_restr]
  have hj1 : (ival E (.var 1)).holds ↔ ((Cof.eq1 (lastVar m)).restr h').holds := by
    rw [holds_ival_iff_face, face_ival_var, hv1, Cof.eq1_restr]
  have hor : (ival E (.or (.neg (.var 1)) (.var 1))).holds ↔
      ((Cof.eq0 (lastVar m)).restr h').holds ∨ ((Cof.eq1 (lastVar m)).restr h').holds := by
    rw [holds_ival_iff_face, face_ival_or, Cof.holds_or, ← holds_ival_iff_face, ← holds_ival_iff_face, hj0, hj1]
  have hnu : Natural S u0 m ρ γ := fun k f => h.nat_u0 f
  have nU : Natural S u0.dshift.dshift n E γ' :=
    Natural.dshift_tail (Natural.dshift_tail (by rw [htt, hγ']; exact hnu.restr X))
  have eU : sem S u0.dshift.dshift n E γ' = res X (sem S u0 m ρ γ) := by
    rw [sem_dshift_tail, sem_dshift_tail, htt, hγ', h.nat_u0]
  have eX : sem S (.app (.fst (e.dsubst τ)) u0.dshift.dshift) n E γ' =
      eqFun n (dat (tgP S e φ ρ γ) n (Hom.snoc X r)) (res X (sem S u0 m ρ γ)) := by
    rw [sem_app_of_nat nU, sem_fst, h.sem_e' hδ hτ0 hτs, eU]; rfl
  have eY : sem S (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) n E γ' =
      eqFun n (dat (tgP S e φ ρ γ) n (Hom.snoc X r)) (res (Hom.snoc X r)
        (transpFillF (gtTL (tgP S T φ ρ γ) (Hom.id m)) (Hom.id (m + 1)) (Cof.restr (ival ρ ψ).face (Hom.id m))
          (res (Hom.id m) (sem S u0 m ρ γ)))) := by
    rw [sem_app_of_nat (nat_ins1 hτ0 hτs (h.nat_tfill hδ) h' r), sem_fst, h.sem_e' hδ hτ0 hτs,
      sem_ins1 hτ0 hτs (h.nat_tfill hδ), h.sem_tfill hδ]; rfl
  have eZ : sem S ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)
      n E γ' = res (Hom.snoc X r) (gtFillA (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ)) := by
    rw [sem_ins1 hτ0 hτs h.sem_fillA.1, h.sem_fillA.2]
  obtain ⟨-, -, htfF⟩ := gt_tfill h.G hψ h.u0mem h.con (h.δid hδ)
  obtain ⟨-, -, -, hfF⟩ := gt_fillA h.G hψ h.u0mem h.con
  have hP := gt_δ_snoc (isCof_ival_face ρ.ext φ) (h.δ_at hδ X) r
  have hu0kv := h.G.elKV h.u0mem
  have aY : (Cof.restr (ival ρ ψ).face X).holds →
      res (Hom.snoc X r) (transpFillF (gtTL (tgP S T φ ρ γ) (Hom.id m)) (Hom.id (m + 1))
        (Cof.restr (ival ρ ψ).face (Hom.id m)) (res (Hom.id m) (sem S u0 m ρ γ))) = res X (sem S u0 m ρ γ) := by
    intro hψX
    rw [htfF X (by rw [Cof.restr_restr, Hom.id_comp]; exact hψX) r, res_id hu0kv]
  have aZ : (Cof.restr (ival ρ ψ).face X).holds →
      res (Hom.snoc X r) (gtFillA (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ)) =
        eqFun n (dat (tgP S e φ ρ γ) n (Hom.snoc X r)) (res X (sem S u0 m ρ γ)) := by
    intro hψX
    rw [hfF X hψX r, gtTube, ungAt, if_pos hP, if_pos (isKV_res _ _)]
  have hno : ((Cof.eq0 (lastVar m)).restr h').holds → ((Cof.eq1 (lastVar m)).restr h').holds → False :=
    fun h0 h1 => DM.zero_ne_one' ((lastVar_zero_of h0).symm.trans (lastVar_one_of h1))
  have einner : ((Cof.eq0 (lastVar m)).restr h').holds ∨ ((Cof.eq1 (lastVar m)).restr h').holds →
      sem S (.split (.neg (.var 1)) (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) (.var 1)
        ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)) n E γ' =
      if ((Cof.eq0 (lastVar m)).restr h').holds then
        sem S (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) n E γ'
      else sem S ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)
        n E γ' := by
    intro hc
    rw [sem_split (by rcases hc with hc | hc; exact Or.inl (hj0.2 hc); exact Or.inr (hj1.2 hc))
      (fun a b => absurd (hj1.1 b) (fun c => hno (hj0.1 a) c))]
    by_cases h0 : ((Cof.eq0 (lastVar m)).restr h').holds
    · rw [if_pos (hj0.2 h0), if_pos h0]
    · rw [if_neg (fun c => h0 (hj0.1 c)), if_neg h0]
  unfold gtΩTube
  simp only [Hom.id_comp]
  by_cases hψX : (Cof.restr (ival ρ ψ).face X).holds
  · rw [sem_split (Or.inl (hψ2.2 hψX)) (fun _ hj => ?_), if_pos (hψ2.2 hψX), if_pos hψX, eX]
    rw [einner (hor.1 hj)]
    split_ifs
    · rw [eY, aY hψX, eX]
    · rw [eZ, aZ hψX, eX]
  · have hj : ((Cof.eq0 (lastVar m)).restr h').holds ∨ ((Cof.eq1 (lastVar m)).restr h').holds := by
      rw [pathFace, Cof.or_restr, Cof.holds_or, Cof.restr_restr, Cof.or_restr, Cof.holds_or] at hh
      exact hh.resolve_left hψX
    rw [sem_split (Or.inr (hor.2 hj)) (fun a => absurd (hψ2.1 a) hψX), if_neg (fun a => hψX (hψ2.1 a)),
      if_neg hψX, einner hj]
    split_ifs
    · rw [eY]
    · rw [eZ]

theorem sem_ωbody {τ : ℕ → I} (hτ0 : τ 0 = .var 0) (hτs : ∀ i, τ (i + 1) = .var (i + 2)) :
    Natural S (Tm.comp (A.dsubst τ) (.or ψ.shift (.or (.neg (.var 0)) (.var 0)))
      (.split ψ.shift.shift (.app (.fst (e.dsubst τ)) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
        (.split (.neg (.var 1)) (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) (.var 1)
          ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)))
      (.app (.fst (e.dinst .zero).dshift) u0.dshift)) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) ∧
    sem S (Tm.comp (A.dsubst τ) (.or ψ.shift (.or (.neg (.var 0)) (.var 0)))
      (.split ψ.shift.shift (.app (.fst (e.dsubst τ)) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
        (.split (.neg (.var 1)) (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) (.var 1)
          ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)))
      (.app (.fst (e.dinst .zero).dshift) u0.dshift)) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) =
    gtΩ (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) (Hom.id m) := by
  have hψ := isCof_ival_face ρ ψ
  have hγw : TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.wk (m + 1)) =
      TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.wk (m + 1)) := rfl
  have eL : lineV S (A.dsubst τ) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) =
      res (gtΩLine (Hom.id m)) (lineV S A m ρ γ) := by
    show sem S (A.dsubst τ) (m + 2) ρ.ext.ext _ = _
    rw [ext_ext_eq, sem_ins1 hτ0 hτs h.Anat, gtΩLine, Hom.id_comp]
  have nL : Natural S (A.dsubst τ) (m + 2) ρ.ext.ext (TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.wk (m + 1))) := by
    rw [ext_ext_eq]; exact nat_ins1 hτ0 hτs h.Anat _ _
  have hok := gt_Ω_ok h.G hψ h.u0mem h.con (h.δid hδ)
  rw [hψ.restr_id] at hok
  have hcc := comp_cond (C := A.dsubst τ) (ρ := ρ.ext) (γ := TEnv.restr γ (Hom.wk m))
    (ψ := .or ψ.shift (.or (.neg (.var 0)) (.var 0)))
    (u := .split ψ.shift.shift (.app (.fst (e.dsubst τ)) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
        (.split (.neg (.var 1)) (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) (.var 1)
          ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)))
    (u0 := .app (.fst (e.dinst .zero).dshift) u0.dshift)
    (by rw [eL]; exact h.Aty.res _) nL
    (by
      rw [eL, face_pathFace, h.ωbase_id hδ]
      exact (hok.congr (isCof_pathFace hψ) fun n h' r hh => (h.sysω_eq hδ hτ0 hτs n h' r hh).symm).res_id)
    (by rw [eL, h.ωbase_id hδ, El_res, Hom.id_comp]; exact gt_ΩBase_mem h.G h.u0mem (h.δid hδ))
    (h.nat_ωbase hδ) (fun x => isKV_res _ _)
  refine ⟨hcc.1.natural, ?_⟩
  rw [hcc.2, eL, compF_res_id, face_pathFace, h.ωbase_id hδ, gtΩ, hψ.restr_id]
  exact compF_congr fun n h' r hh => h.sysω_eq hδ hτ0 hτs n h' r hh

theorem sem_ω {τ : ℕ → I} (hτ0 : τ 0 = .var 0) (hτs : ∀ i, τ (i + 1) = .var (i + 2)) :
    sem S (.plam (Tm.comp (A.dsubst τ) (.or ψ.shift (.or (.neg (.var 0)) (.var 0)))
      (.split ψ.shift.shift (.app (.fst (e.dsubst τ)) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
        (.split (.neg (.var 1)) (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) (.var 1)
          ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)))
      (.app (.fst (e.dinst .zero).dshift) u0.dshift))) m ρ γ =
    gtω (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) (Hom.id m) := by
  rw [sem_plam (h.sem_ωbody hδ hτ0 hτs).1, lineV, (h.sem_ωbody hδ hτ0 hτs).2]; rfl

end δ

/-- `δ` at a restricted point. -/
theorem δ_restr (h : TGCond S A φ T e ψ u0 m ρ γ) {f : Hom k m} (hf : ((gtδ (tgφ ρ φ)).restr f).holds) :
    (Cof.forall0 (tgφ (ρ.restr f) φ)).holds := by
  rw [tgφ_restr, ← Cof.forall0_restr]; exact hf

theorem sem_t1'_at (h : TGCond S A φ T e ψ u0 m ρ γ) {f : Hom k m} (hf : ((gtδ (tgφ ρ φ)).restr f).holds) :
    sem S (.transp T ψ u0) k (ρ.restr f) (TEnv.restr γ f) = gtT1' (tgP S T φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) f := by
  rw [(h.restr f).sem_t1' (h.δ_restr hf), tgP_restr, face_ival_restr, h.nat_u0, gd_T1', Hom.comp_id]

theorem sem_ω_at (h : TGCond S A φ T e ψ u0 m ρ γ) {f : Hom k m} (hf : ((gtδ (tgφ ρ φ)).restr f).holds)
    {τ : ℕ → I} (hτ0 : τ 0 = .var 0) (hτs : ∀ i, τ (i + 1) = .var (i + 2)) :
    sem S (.plam (Tm.comp (A.dsubst τ) (.or ψ.shift (.or (.neg (.var 0)) (.var 0)))
      (.split ψ.shift.shift (.app (.fst (e.dsubst τ)) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
        (.split (.neg (.var 1)) (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) (.var 1)
          ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)))
      (.app (.fst (e.dinst .zero).dshift) u0.dshift))) k (ρ.restr f) (TEnv.restr γ f) =
    gtω (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) f := by
  rw [(h.restr f).sem_ω (h.δ_restr hf) hτ0 hτs, line_restr h.Anat f, tgφ_restr, tgP_restr, tgP_restr,
    face_ival_restr, h.nat_u0, gd_ω h.G (isCof_ival_face ρ ψ) h.u0mem h.con, Hom.comp_id]

theorem sem_a1'_at (h : TGCond S A φ T e ψ u0 m ρ γ) (f : Hom k m) :
    sem S (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)) k
      (ρ.restr f) (TEnv.restr γ f) = res f (gtA1' (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ)) := by
  rw [h.nat_a1' k f, h.sem_a1']

/-! ### On `φ(1)` -/

section φ1

variable (h : TGCond S A φ T e ψ u0 m ρ γ) (h1 : (Cof.restr (tgφ ρ φ) (eO m)).holds)
include h h1

theorem h1' : (Cof.restr (tgφ ρ φ) ((eO m).comp (Hom.id m))).holds := by rw [Hom.comp_id]; exact h1

theorem env1 : ρ.ext.restr (eO m) = ρ.cons (ival ρ .one) := by rw [ival_one, IEnv.ext_restr_endpt]

theorem γ1 : TEnv.restr (TEnv.restr γ (Hom.wk m)) (eO m) = γ := by
  rw [TEnv.restr_restr, Hom.wk_comp_endpt, TEnv.restr_id_of_kv h.kv]

theorem sem_A1 : sem S (A.dinst .one) m ρ γ = gtAA1 (lineV S A m ρ γ) (Hom.id m) := by
  rw [sem_dinst, ival_one, line_endpt h.kv h.Anat, gtAA1, Hom.comp_id]

theorem nat_A1 : Natural S (A.dinst .one) m ρ γ :=
  Natural.dinst (by rw [ival_one]; exact line_endpt_nat h.kv h.Anat _)

theorem sem_T1 : sem S (T.dinst .one) m ρ γ = gtT1 (tgP S T φ ρ γ) (Hom.id m) := by
  rw [sem_dinst, ← h.env1 h1, gtT1, Hom.comp_id, dat_partialKV_holds h1, faceVals, h.γ1 h1]

theorem sem_e1 : sem S (e.dinst .one) m ρ γ = gtE1 (tgP S e φ ρ γ) (Hom.id m) := by
  rw [sem_dinst, ← h.env1 h1, gtE1, Hom.comp_id, dat_partialKV_holds h1, faceVals, h.γ1 h1]

theorem nat_T1 : Natural S (T.dinst .one) m ρ γ := by
  apply Natural.dinst
  intro k f
  have := h.fn.1 m (eO m) h1 k f
  rwa [h.env1 h1, h.γ1 h1] at this

theorem nat_e1 : Natural S (e.dinst .one) m ρ γ := by
  apply Natural.dinst
  intro k f
  have := h.fn.2 m (eO m) h1 k f
  rwa [h.env1 h1, h.γ1 h1] at this

theorem nat_fst_e1 : Natural S (.fst (e.dinst .one)) m ρ γ := by
  intro k f
  rw [sem_fst, sem_fst, h.nat_e1 h1 k f, h.sem_e1 h1, fstV_res_of_pair (gt_e1_pair h.G (h.h1' h1))]

theorem sem_fib :
    sem S (Tm.fiber (T.dinst .one) (A.dinst .one) (.fst (e.dinst .one))
      (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0))) m ρ γ =
    gtFib (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) (Hom.id m) := by
  obtain ⟨hT, hA, hp, -⟩ := gt_e1 h.G (h.h1' h1)
  rw [sem_fiber (h.nat_T1 h1) (h.nat_A1 h1) (h.nat_fst_e1 h1) h.nat_a1' (by rw [h.sem_T1 h1]; exact hT)
    (by rw [(h.sem_A1 h1)]; exact hA) (by rw [sem_fst, h.sem_e1 h1, h.sem_T1 h1, (h.sem_A1 h1)]; exact hp),
    h.sem_T1 h1, (h.sem_A1 h1), sem_fst, h.sem_e1 h1, h.sem_a1', gtFib, res_id h.a1'kv]

theorem sem_c :
    sem S (.app (.snd (e.dinst .one))
      (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0))) m ρ γ =
    gtC (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) (Hom.id m) := by
  rw [sem_app_of_nat h.nat_a1', sem_snd, h.sem_e1 h1, h.sem_a1', gtC, res_id h.a1'kv]

theorem nat_fib :
    Natural S (Tm.fiber (T.dinst .one) (A.dinst .one) (.fst (e.dinst .one))
      (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0))) m ρ γ := by
  obtain ⟨hT, hA, hp, -⟩ := gt_e1 h.G (h.h1' h1)
  exact natural_fiber (h.nat_T1 h1) (h.nat_A1 h1) (h.nat_fst_e1 h1) h.nat_a1' (by rw [h.sem_T1 h1]; exact hT)
    (by rw [h.sem_A1 h1]; exact hA) (by rw [sem_fst, h.sem_e1 h1, h.sem_T1 h1, h.sem_A1 h1]; exact hp)

end φ1

theorem h1_restr (h : TGCond S A φ T e ψ u0 m ρ γ) {f : Hom k m} (hf : (Cof.restr (tgφ ρ φ) ((eO m).comp f)).holds) :
    (Cof.restr (tgφ (ρ.restr f) φ) (eO k)).holds := by
  rw [tgφ_restr, Cof.restr_restr, TranspPi.lift_comp_endpt1]; exact hf

theorem sem_c_at (h : TGCond S A φ T e ψ u0 m ρ γ) {f : Hom k m} (hf : (Cof.restr (tgφ ρ φ) ((eO m).comp f)).holds) :
    sem S (.app (.snd (e.dinst .one))
      (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0))) k
      (ρ.restr f) (TEnv.restr γ f) =
    gtC (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) f := by
  rw [(h.restr f).sem_c (h.h1_restr hf), line_restr h.Anat f, tgφ_restr, tgP_restr, face_ival_restr, h.nat_u0,
    gd_C h.G (isCof_ival_face ρ ψ) h.u0mem h.con, Hom.comp_id]

theorem sem_fib_at (h : TGCond S A φ T e ψ u0 m ρ γ) {f : Hom k m} (hf : (Cof.restr (tgφ ρ φ) ((eO m).comp f)).holds) :
    sem S (Tm.fiber (T.dinst .one) (A.dinst .one) (.fst (e.dinst .one))
      (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0))) k
      (ρ.restr f) (TEnv.restr γ f) =
    gtFib (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) f := by
  rw [(h.restr f).sem_fib (h.h1_restr hf), line_restr h.Anat f, tgφ_restr, tgP_restr, tgP_restr, face_ival_restr,
    h.nat_u0, gd_Fib h.G (isCof_ival_face ρ ψ) h.u0mem h.con, Hom.comp_id]

theorem nat_fst_c (h : TGCond S A φ T e ψ u0 m ρ γ) (h1 : (Cof.restr (tgφ ρ φ) (eO m)).holds) :
    Natural S (.fst (.app (.snd (e.dinst .one))
      (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)))) m ρ γ := by
  intro k f
  have hf : (Cof.restr (tgφ ρ φ) ((eO m).comp f)).holds := by
    rw [← Cof.restr_restr]; exact ((isCof_ival_face ρ.ext φ).restr _).holds_restr h1 f
  obtain ⟨-, -, -, hpair⟩ := gt_c h.G (isCof_ival_face ρ ψ) h.u0mem h.con (h.h1' h1)
  rw [sem_fst, sem_fst, h.sem_c_at hf, h.sem_c h1, ← fstV_res_of_pair hpair f,
    gt_C_res h.G (isCof_ival_face ρ ψ) h.u0mem h.con (h.h1' h1), Hom.id_comp]

/-! ### The partial element of the fiber -/

theorem sem_pairδ_at (h : TGCond S A φ T e ψ u0 m ρ γ) {n : ℕ} {f : Hom n m}
    (hf : ((gtδ (tgφ ρ φ)).restr f).holds) (r : DM n)
    {τ : ℕ → I} (hτ0 : τ 0 = .var 0) (hτs : ∀ i, τ (i + 1) = .var (i + 2)) :
    sem S (.pair (Tm.transp T ψ u0).dshift (Tm.plam (Tm.comp (A.dsubst τ) (.or ψ.shift (.or (.neg (.var 0)) (.var 0)))
      (.split ψ.shift.shift (.app (.fst (e.dsubst τ)) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
        (.split (.neg (.var 1)) (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) (.var 1)
          ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)))
      (.app (.fst (e.dinst .zero).dshift) u0.dshift))).dshift) n ((ρ.restr f).cons r) (TEnv.restr γ f) =
    pairV n (gtT1' (tgP S T φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) f)
      (gtω (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) f) := by
  have hP1 : (Cof.restr (tgφ ρ φ) ((eO m).comp f)).holds := by
    rw [← snoc_one_eq]; exact gt_δ_snoc (isCof_ival_face ρ.ext φ) hf _
  obtain ⟨hT, -, -, -⟩ := gt_e1 h.G hP1
  have e1 := h.sem_t1'_at hf
  have e2 := h.sem_ω_at hf hτ0 hτs
  rw [sem_pair_of_kv (by rw [sem_dshift_cons, e1]; exact hT.elKV _ _ _ (gt_T1'_mem h.G (isCof_ival_face ρ ψ)
      h.u0mem h.con hf)) (by rw [sem_dshift_cons, e2]; unfold gtω pathOfLine; exact isKV_mkKV _),
    sem_dshift_cons, sem_dshift_cons, e1, e2]

theorem sem_pairψ_at (h : TGCond S A φ T e ψ u0 m ρ γ) {n : ℕ} (f : Hom n m) (r : DM n) :
    sem S (.pair u0.dshift (.plam
      (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dshift.dshift))
      n ((ρ.restr f).cons r) (TEnv.restr γ f) =
    pairV n (res f (sem S u0 m ρ γ)) (pathOfLine n (res (Hom.wk n)
      (res f (gtA1' (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ))))) := by
  set E := (ρ.restr f).cons r
  have htt : E.ext.tail.tail = ρ.restr (f.comp (Hom.wk n)) := by
    show ((ρ.restr f).restr (Hom.wk n)) = _; rw [IEnv.restr_restr]
  have hγ : TEnv.restr (TEnv.restr γ f) (Hom.wk n) = TEnv.restr γ (f.comp (Hom.wk n)) := TEnv.restr_restr _ _ _
  have hnat : Natural S (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dshift.dshift
      (n + 1) E.ext (TEnv.restr (TEnv.restr γ f) (Hom.wk n)) :=
    Natural.dshift_tail (Natural.dshift_tail (by rw [htt, hγ]; exact h.nat_a1'.restr _))
  have ev : lineV S (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dshift.dshift
      n E (TEnv.restr γ f) = res (Hom.wk n) (res f (gtA1' (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ))) := by
    rw [lineV, sem_dshift_tail, sem_dshift_tail, htt, hγ, h.sem_a1'_at, res_res]
  rw [sem_pair_of_kv (by rw [sem_dshift_cons, h.nat_u0]; exact isKV_res _ _)
      (by rw [sem_plam hnat, ev]; unfold pathOfLine; exact isKV_mkKV _),
    sem_dshift_cons, h.nat_u0, sem_plam hnat, ev]

theorem tyCode_fib (h : TGCond S A φ T e ψ u0 m ρ γ) (h1 : (Cof.restr (tgφ ρ φ) (eO m)).holds) :
    TyCode m (gtFib (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) (Hom.id m)) := by
  obtain ⟨hT, hA, hp, -⟩ := gt_e1 h.G (h.h1' h1)
  have hty := (h.he m (eO m) h1).2
  unfold TyOK at hty
  have hTn : Natural S T m (ρ.ext.restr (eO m)) (TEnv.restr (TEnv.restr γ (Hom.wk m)) (eO m)) := by
    intro k f
    have := h.fn.1 m (eO m) h1 k f
    exact this
  rw [sem_equiv hTn (h.Anat.restr _)] at hty
  have eT : sem S T m (ρ.ext.restr (eO m)) (TEnv.restr (TEnv.restr γ (Hom.wk m)) (eO m)) = gtT1 (tgP S T φ ρ γ) (Hom.id m) := by
    rw [gtT1, Hom.comp_id, dat_partialKV_holds h1]; rfl
  have eA : sem S A m (ρ.ext.restr (eO m)) (TEnv.restr (TEnv.restr γ (Hom.wk m)) (eO m)) = gtAA1 (lineV S A m ρ γ) (Hom.id m) := by
    rw [h.Anat m (eO m), gtAA1, Hom.comp_id]
  rw [eT, eA, equivCode_eq_equivM hT hA] at hty
  have hy := gt_A1'_g h.G (isCof_ival_face ρ ψ) h.u0mem h.con (Hom.id m)
  rw [res_id h.a1'kv] at hy
  have := tyCode_fiberM hT.kv hA.kv hty hp hy
  rwa [gtFib, res_id h.a1'kv]

theorem sem_extTube (h : TGCond S A φ T e ψ u0 m ρ γ) (h1 : (Cof.restr (tgφ ρ φ) (eO m)).holds)
    {τ : ℕ → I} (hτ0 : τ 0 = .var 0) (hτs : ∀ i, τ (i + 1) = .var (i + 2))
    (n : ℕ) (h' : Hom n m) (r : DM n)
    (hh : ((Cof.or (gtδ (tgφ ρ φ)) (ival ρ ψ).face).restr h').holds) :
    tubeV S (.split (I.forall0 φ).shift
      (.papp (.app (Tm.snd (.app (.snd (e.dinst .one))
        (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)))).dshift
        (.pair (Tm.transp T ψ u0).dshift (Tm.plam (Tm.comp (A.dsubst τ) (.or ψ.shift (.or (.neg (.var 0)) (.var 0)))
          (.split ψ.shift.shift (.app (.fst (e.dsubst τ)) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
            (.split (.neg (.var 1)) (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) (.var 1)
              ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)))
          (.app (.fst (e.dinst .zero).dshift) u0.dshift))).dshift)) (.var 0))
      ψ.shift
      (.papp (.app (Tm.snd (.app (.snd (e.dinst .one))
        (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)))).dshift
        (.pair u0.dshift (.plam
          (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dshift.dshift)))
        (.var 0))) ρ γ n h' r =
    gtExtTube (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ)
      (Hom.id m) n h' r := by
  have hψ := isCof_ival_face ρ ψ
  have hδc := gt_δ_cof (isCof_ival_face ρ.ext φ)
  have hf : (Cof.restr (tgφ ρ φ) ((eO m).comp h')).holds := by
    rw [← Cof.restr_restr]; exact ((isCof_ival_face ρ.ext φ).restr _).holds_restr h1 h'
  obtain ⟨-, -, -, hpair⟩ := gt_c h.G hψ h.u0mem h.con (h.h1' h1)
  simp only [tubeV]
  set E := (ρ.restr h').cons r
  have hδ' : (ival E (I.forall0 φ).shift).holds ↔ ((gtδ (tgφ ρ φ)).restr h').holds := by
    rw [ival_shift, IEnv.tail_cons, ← holds_face_restr_iff, face_ival_forall0]; rfl
  have hψ' : (ival E ψ.shift).holds ↔ (Cof.restr (ival ρ ψ).face h').holds := by
    rw [ival_shift, IEnv.tail_cons, ← holds_face_restr_iff]
  have esc : sem S (Tm.snd (.app (.snd (e.dinst .one))
      (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)))).dshift
      n E (TEnv.restr γ h') =
      res h' (sndV m (gtC (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) (Hom.id m))) := by
    rw [sem_dshift_cons, sem_snd, h.sem_c_at hf, ← sndV_res_of_pair hpair,
      gt_C_res h.G hψ h.u0mem h.con (h.h1' h1), Hom.id_comp]
  have nPδ : ((gtδ (tgφ ρ φ)).restr h').holds →
      Natural S (.pair (Tm.transp T ψ u0).dshift (Tm.plam (Tm.comp (A.dsubst τ) (.or ψ.shift (.or (.neg (.var 0)) (.var 0)))
        (.split ψ.shift.shift (.app (.fst (e.dsubst τ)) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
          (.split (.neg (.var 1)) (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) (.var 1)
            ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)))
        (.app (.fst (e.dinst .zero).dshift) u0.dshift))).dshift) n E (TEnv.restr γ h') := by
    intro hδh k g
    have hδg : ((gtδ (tgφ ρ φ)).restr (h'.comp g)).holds := cof_holds_comp hδc hδh g
    rw [IEnv.cons_restr, IEnv.restr_restr, TEnv.restr_restr, h.sem_pairδ_at hδg _ hτ0 hτs,
      h.sem_pairδ_at hδh r hτ0 hτs, res_pairV, gt_T1'_res h.G hψ h.u0mem h.con hδh,
      gt_ω_res h.G hψ h.u0mem h.con hδh]
  have nPψ : Natural S (.pair u0.dshift (.plam
      (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dshift.dshift))
      n E (TEnv.restr γ h') := by
    intro k g
    rw [IEnv.cons_restr, IEnv.restr_restr, TEnv.restr_restr, h.sem_pairψ_at, h.sem_pairψ_at, gt_refl_res]
  unfold gtExtTube
  simp only [Hom.id_comp]
  have eψ : sem S (.papp (.app (Tm.snd (.app (.snd (e.dinst .one))
        (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)))).dshift
        (.pair u0.dshift (.plam
          (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dshift.dshift)))
        (.var 0)) n E (TEnv.restr γ h') =
      pappV n (appV n (res h' (sndV m (gtC (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) (Hom.id m))))
        (pairV n (res h' (sem S u0 m ρ γ)) (pathOfLine n (res (Hom.wk n)
          (res h' (gtA1' (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ))))))) r := by
    rw [sem_papp, sem_app_of_nat nPψ, esc, h.sem_pairψ_at]; rfl
  by_cases hδh : ((gtδ (tgφ ρ φ)).restr h').holds
  · have eδ : sem S (.papp (.app (Tm.snd (.app (.snd (e.dinst .one))
          (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)))).dshift
          (.pair (Tm.transp T ψ u0).dshift (Tm.plam (Tm.comp (A.dsubst τ) (.or ψ.shift (.or (.neg (.var 0)) (.var 0)))
            (.split ψ.shift.shift (.app (.fst (e.dsubst τ)) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
              (.split (.neg (.var 1)) (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) (.var 1)
                ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)))
            (.app (.fst (e.dinst .zero).dshift) u0.dshift))).dshift)) (.var 0)) n E (TEnv.restr γ h') =
        pappV n (appV n (res h' (sndV m (gtC (lineV S A m ρ γ) (tgφ ρ φ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) (Hom.id m))))
          (pairV n (gtT1' (tgP S T φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) h')
            (gtω (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) h'))) r := by
      rw [sem_papp, sem_app_of_nat (nPδ hδh), esc, h.sem_pairδ_at hδh r hτ0 hτs]; rfl
    rw [sem_split (Or.inl (hδ'.2 hδh)) (fun _ hψh => by
        rw [eδ, eψ, gt_pair_psi h.G hψ h.u0mem h.con hδh (hψ'.1 hψh)]),
      if_pos (hδ'.2 hδh), if_pos hδh, eδ]
  · have hψh : (Cof.restr (ival ρ ψ).face h').holds := by
      rw [Cof.or_restr, Cof.holds_or] at hh; exact hh.resolve_left hδh
    rw [sem_split (Or.inr (hψ'.2 hψh)) (fun a => absurd (hδ'.1 a) hδh), if_neg (fun a => hδh (hδ'.1 a)),
      if_neg hδh, eψ]

theorem sem_ext (h : TGCond S A φ T e ψ u0 m ρ γ) (h1 : (Cof.restr (tgφ ρ φ) (eO m)).holds)
    {τ : ℕ → I} (hτ0 : τ 0 = .var 0) (hτs : ∀ i, τ (i + 1) = .var (i + 2)) :
    HcompCond S (Tm.fiber (T.dinst .one) (A.dinst .one) (.fst (e.dinst .one))
      (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)))
      (.or (I.forall0 φ) ψ)
      (.split (I.forall0 φ).shift
        (.papp (.app (Tm.snd (.app (.snd (e.dinst .one))
          (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)))).dshift
          (.pair (Tm.transp T ψ u0).dshift (Tm.plam (Tm.comp (A.dsubst τ) (.or ψ.shift (.or (.neg (.var 0)) (.var 0)))
            (.split ψ.shift.shift (.app (.fst (e.dsubst τ)) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
              (.split (.neg (.var 1)) (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) (.var 1)
                ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)))
            (.app (.fst (e.dinst .zero).dshift) u0.dshift))).dshift)) (.var 0))
        ψ.shift
        (.papp (.app (Tm.snd (.app (.snd (e.dinst .one))
          (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)))).dshift
          (.pair u0.dshift (.plam
            (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dshift.dshift)))
          (.var 0)))
      (.fst (.app (.snd (e.dinst .one))
        (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)))) m ρ γ ∧
    hcompAt (sem S (Tm.fiber (T.dinst .one) (A.dinst .one) (.fst (e.dinst .one))
      (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0))) m ρ γ)
      (Hom.id m) (ival ρ (.or (I.forall0 φ) ψ)).face
      (tubeV S (.split (I.forall0 φ).shift
        (.papp (.app (Tm.snd (.app (.snd (e.dinst .one))
          (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)))).dshift
          (.pair (Tm.transp T ψ u0).dshift (Tm.plam (Tm.comp (A.dsubst τ) (.or ψ.shift (.or (.neg (.var 0)) (.var 0)))
            (.split ψ.shift.shift (.app (.fst (e.dsubst τ)) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
              (.split (.neg (.var 1)) (.app (.fst (e.dsubst τ)) ((Tm.transpFill T ψ u0).dsubst τ)) (.var 1)
                ((Tm.fill A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dsubst τ)))
            (.app (.fst (e.dinst .zero).dshift) u0.dshift))).dshift)) (.var 0))
        ψ.shift
        (.papp (.app (Tm.snd (.app (.snd (e.dinst .one))
          (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)))).dshift
          (.pair u0.dshift (.plam
            (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)).dshift.dshift)))
          (.var 0))) ρ γ)
      (sem S (.fst (.app (.snd (e.dinst .one))
        (Tm.comp A ψ (.unglue φ e u0.dshift) (.unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0)))) m ρ γ) =
    gtExt (lineV S A m ρ γ) (tgφ ρ φ) (tgP S T φ ρ γ) (tgP S e φ ρ γ) (ival ρ ψ).face (sem S u0 m ρ γ) (Hom.id m) := by
  have hψ := isCof_ival_face ρ ψ
  have hface : (ival ρ (.or (I.forall0 φ) ψ)).face = Cof.or (gtδ (tgφ ρ φ)) (ival ρ ψ).face := by
    rw [face_ival_or, face_ival_forall0]; rfl
  obtain ⟨-, hcen, -, -⟩ := gt_c h.G hψ h.u0mem h.con (h.h1' h1)
  have hok := gt_ext_tube_ok h.G hψ h.u0mem h.con (h.h1' h1)
  rw [(gt_δ_cof (isCof_ival_face ρ.ext φ)).restr_id, hψ.restr_id] at hok
  refine ⟨⟨?_, ?_, ?_, h.nat_fib h1, h.nat_fst_c h1⟩, ?_⟩
  · rw [h.sem_fib h1]; exact h.tyCode_fib h1
  · rw [h.sem_fib h1, sem_fst, h.sem_c h1, hface]
    exact hok.congr ((gt_δ_cof (isCof_ival_face ρ.ext φ)).or hψ) fun n h' r hh => (h.sem_extTube h1 hτ0 hτs n h' r hh).symm
  · rw [h.sem_fib h1, sem_fst, h.sem_c h1]; exact hcen
  · rw [h.sem_fib h1, sem_fst, h.sem_c h1, hface, gtExt, (gt_δ_cof (isCof_ival_face ρ.ext φ)).restr_id, hψ.restr_id]
    exact hcompAt_congr fun n h' r hh => h.sem_extTube h1 hτ0 hτs n h' r hh

end TGCond

end tg

end

end Model
