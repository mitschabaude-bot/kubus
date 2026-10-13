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

end TGCond

end tg

end

end Model
