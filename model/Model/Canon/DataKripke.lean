import Model.Canon.DataTy

/-!
# Canonicity: inductive types, restriction
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' n m : ℕ}

theorem substList_isub {A : Tm} {N : ℕ} (hA : A.closedB N 0 = true) (L : List Tm) (σ : ISub k' k) :
    (A.substList L).isub σ = A.substList (L.map (·.isub σ)) := by
  simp only [Tm.isub, Tm.substList, subst_subst]
  apply closed_subst_eq A N 0 _ _ _ _ hA (fun x _ => ?_) (fun i hi => absurd hi (Nat.not_lt_zero _))
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.length_map]
  cases h : L[x]? <;> rfl

theorem ofList_isub (L : List Tm) (σ : ISub k' k) : (Tm.ofList L).isub σ = Tm.ofList (L.map (·.isub σ)) :=
  ofList_subst L _ _

theorem toList_isub {t : Tm} (h : t = Tm.ofList t.toList) (σ : ISub k' k) :
    (t.isub σ).toList = t.toList.map (·.isub σ) := toList_subst h _ _

/-! ### Valid prefixes under restriction -/

theorem ValidPre.ptValid {Θ : SData m} {h : Hom k m} {c j : ℕ} {pre : List V}
    (hv : ValidPre (Θ.restr h) c j pre) : Θ.PtValid c k (h.comp (Hom.id k)) pre := by
  obtain ⟨hc, -, -, hp⟩ := hv
  intro i hi hr
  have := hp i hi
  simp only [argSet] at this
  have hr' : (Θ.restr h).ctors[c].isRec i = false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (l := Θ.ctors) hc, Option.getD_some] at hr; exact hr
  rw [if_neg (by simp [hr'])] at this
  exact this

theorem validPre_res {Θ : SData m} (hΘ : Θ.Good) {h : Hom k m} {c j : ℕ} {pre : List V}
    (hv : ValidPre (Θ.restr h) c j pre) (g : Hom k' k) :
    ValidPre (Θ.restr (h.comp g)) c j (pre.map (res g)) ∧
      tyLook (shapeV (Θ.restr (h.comp g))) c j (pre.map (res g)) = res g (tyLook (shapeV (Θ.restr h)) c j pre) := by
  have hpv := hv.ptValid
  obtain ⟨hc, hj, hl, hp⟩ := hv
  have hv' : ValidPre (Θ.restr (h.comp g)) c j (pre.map (res g)) := by
    refine ⟨hc, hj, by simp [hl], fun i hi => ?_⟩
    simp only [List.length_map] at hi
    have := hp i hi
    simp only [argSet, List.getElem_map, show (Θ.restr (h.comp g)).ctors = Θ.ctors from rfl,
      show (Θ.restr h).ctors = Θ.ctors from rfl] at this ⊢
    split
    · rename_i hr
      rw [if_pos hr] at this
      rw [mem_delemSet, delem_restr_iff] at this ⊢
      have := this.res hΘ.resClosed k' g
      simpa using this
    · rename_i hr
      rw [if_neg hr] at this
      have hpi : Θ.PtValid c k (h.comp (Hom.id k)) (pre.take i) := hpv.take i
      have h2 := hΘ.resClosed c i k (h.comp (Hom.id k)) (pre.take i) pre[i] hpi this k' g
      show res g pre[i] ∈ El (Θ.ty c i k' ((h.comp g).comp (Hom.id k')) ((pre.map (res g)).take i)) (Hom.id k')
      rw [Hom.comp_id, List.map_take.symm]
      rwa [Hom.comp_id] at h2
  refine ⟨hv', ?_⟩
  rw [tyLook_eq hv', tyLook_eq ⟨hc, hj, hl, hp⟩]
  show Θ.ty c j k' ((h.comp g).comp (Hom.id k')) (pre.map (res g)) =
    res g (Θ.ty c j k (h.comp (Hom.id k)) pre)
  rw [hΘ.nat c j k _ pre hpv k' g]; simp only [Hom.comp_id]

/-! ### Computable elements under restriction -/

theorem DR.typed {m : ℕ} {d : ℕ} {D : DataDecl} {Mem : (k : ℕ) → Hom k m → Tm → Prop}
    {P : (k : ℕ) → Hom k m → ℕ → ℕ → List V → Tm → Tm → Prop} {k : ℕ} {f : Hom k m} {A t : Tm}
    (h : DR S d D Mem P k f A t) : HasTy S k .one [] t A := by
  cases h with
  | con _ _ _ _ _ _ he => exact HasTy.eqL he
  | hcomp _ _ _ _ _ _ he => exact HasTy.eqL he

theorem DR.mem {m : ℕ} {d : ℕ} {D : DataDecl} {Mem : (k : ℕ) → Hom k m → Tm → Prop}
    {P : (k : ℕ) → Hom k m → ℕ → ℕ → List V → Tm → Tm → Prop} {k : ℕ} {f : Hom k m} {A t : Tm}
    (h : DR S d D Mem P k f A t) : Mem k f t := by
  cases h with
  | con hm => exact hm
  | hcomp hm => exact hm

section dr

variable (hW : WfSig S) {k0 : ℕ} {Θ : SData m} (hΘ : Θ.Good) (f : Hom k0 m)
include hW

include hΘ in
theorem dataMem_isub {g : Hom k k0} {t A : Tm} (ht : HasTy S k .one [] t A) (hm : dataMem S Θ f k g t)
    (σ : ISub k' k) : dataMem S Θ f k' (g.comp σ.hom) (t.isub σ) := by
  unfold dataMem at hm ⊢
  rw [semK_isubS hW ht, mem_delemSet, delem_restr_iff]
  rw [mem_delemSet, delem_restr_iff] at hm
  have := hm.res hΘ.resClosed k' σ.hom
  simpa [Hom.comp_assoc] using this

omit hW in
include hΘ in
theorem dataP_isub (ihT : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → KR S n (Θ.ty c j n g pre))
    {g : Hom k k0} {c j : ℕ} {pre : List V} {A a : Tm} (hp : dataP S Θ f k g c j pre A a) (σ : ISub k' k) :
    dataP S Θ f k' (g.comp σ.hom) c j (pre.map (res σ.hom)) (A.isub σ) (a.isub σ) := by
  unfold dataP at hp ⊢
  have hv := validPre_of_el hp
  obtain ⟨-, heq⟩ := validPre_res hΘ hv σ.hom
  rw [← Hom.comp_assoc, heq]
  rw [tyLook_eq hv] at hp ⊢
  have hY := ihT c j k _ pre hv.ptValid
  have hne : Θ.ty c j k ((f.comp g).comp (Hom.id k)) pre ≠ ∅ := by
    intro h0; rw [show (Θ.restr (f.comp g)).ty c j k (Hom.id k) pre = Θ.ty c j k ((f.comp g).comp (Hom.id k)) pre
      from rfl, h0, Comp_empty] at hp; exact hp
  show (Comp S (res σ.hom (Θ.ty c j k ((f.comp g).comp (Hom.id k)) pre)) k' k' (Hom.id k')).el _ _
  rw [← Comp_eq_res hne]
  have := ((hY k (Hom.id k) k' σ A a).2 hp)
  rwa [Hom.id_comp] at this

omit hW in
theorem dataD_of_ctor {d c : ℕ} {C : Ctor} (h : (dataD S d).ctors[c]? = some C) :
    ∃ D, S[d]? = some (.data D) ∧ dataD S d = D := by
  unfold dataD at h ⊢
  cases hS : S[d]? with
  | none => simp only [hS] at h; exact absurd h (by rw [show (default : DataDecl).ctors = [] from rfl]; simp)
  | some e =>
    cases e with
    | data D => exact ⟨D, rfl, rfl⟩
    | defn t A => simp only [hS] at h; exact absurd h (by rw [show (default : DataDecl).ctors = [] from rfl]; simp)

omit hW in
theorem argTy_point {C : Ctor} {j : ℕ} (hj : j < C.args.length) (hr : C.isRec j = false) :
    ∃ A, C.args[j]? = some (.point A) := by
  cases h' : C.args[j]'hj with
  | point A => exact ⟨A, by rw [List.getElem?_eq_getElem hj, h']⟩
  | recur => simp [Ctor.isRec, List.getElem?_eq_getElem hj, h'] at hr

include hΘ in
theorem DR.isub (ihT : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → KR S n (Θ.ty c j n g pre))
    {d : ℕ} {k : ℕ} {g : Hom k k0} {A t : Tm}
    (h : DR S d (dataD S d) (dataMem S Θ f) (dataP S Θ f) k g A t) :
    ∀ k' (σ : ISub k' k), DR S d (dataD S d) (dataMem S Θ f) (dataP S Θ f) k' (g.comp σ.hom) (A.isub σ) (t.isub σ) := by
  induction h with
  | @con k g A t ps c C args rs hm hC hrs hsc hpl hAeq he hlen hrec hpt ihrec =>
    intro k' σ
    obtain ⟨D, hd, hD⟩ := dataD_of_ctor hC
    have hsyn := ((sigOK_of_wfSig _ S rfl hW).2 d D hd).1
    have hargTy : ∀ j (hj : j < args.length), C.isRec j = false →
        ∃ N, (C.argTy d (dataD S d).params.length j).closedB N 0 = true := by
      intro j hj hr
      obtain ⟨A0, hA0⟩ := argTy_point (by omega) hr
      rw [hD] at hC
      have := (hsyn.2.2.1 c C hC j A0 hA0).1
      rw [show C.argTy d (dataD S d).params.length j = A0 by simp [Ctor.argTy, hA0]]
      exact ⟨_, this⟩
    have htyArg : ∀ j (hj : j < args.length), HasTy S k .one [] args[j] (if C.isRec j then .data d ps else
        (C.argTy d (dataD S d).params.length j).substList ((args.take j).reverse ++ ps.toList.reverse)) := by
      intro j hj
      cases hr : C.isRec j
      · simp only [Bool.false_eq_true, if_false]; exact (Comp_el_typed (hpt j hj hr)).1
      · simp only [if_true]; exact (hrec j hj hr).typed
    have hsem : ∀ j, j ≤ args.length → ((args.map (·.isub σ)).take j).map (semK S k') =
        ((args.take j).map (semK S k)).map (res σ.hom) := by
      intro j hj
      apply List.ext_getElem (by simp) fun i h1 h2 => ?_
      simp only [List.length_map, List.length_take] at h1
      simp only [List.getElem_map, List.getElem_take]
      have := htyArg i (by omega)
      split at this <;> exact semK_isubS hW this σ
    refine DR.con (ps := ps.isub σ) (args := args.map (·.isub σ)) (rs := rs.map (·.subst σ.τ))
      (dataMem_isub hW hΘ f (HasTy.eqL he) hm σ) hC (by simp [hrs])
      (fun r hr => by obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr; exact I.scoped_subst (hsc r0 hr0) σ.sc)
      (isList_subst hpl _ _) (hAeq.isub hW σ) ?_ (by simp [hlen]) (fun j hj hr => ?_) (fun j hj hr => ?_)
    · have := EqTm.isubS hW he σ
      rwa [show (Tm.con d c ps (Tm.ofList args) rs).isub σ =
        Tm.con d c (ps.isub σ) (Tm.ofList (args.map (·.isub σ))) (rs.map (·.subst σ.τ)) from by
          simp only [Tm.isub, Tm.subst]; rw [ofList_subst]] at this
    · simp only [List.length_map] at hj
      rw [List.getElem_map]
      exact ihrec j hj hr k' σ
    · simp only [List.length_map] at hj
      obtain ⟨N, hN⟩ := hargTy j hj hr
      have := dataP_isub hΘ f ihT (hpt j hj hr) σ
      rw [← hsem j hj.le, substList_isub hN] at this
      rw [List.getElem_map]
      convert this using 2
      rw [List.map_append, List.map_reverse, List.map_reverse, List.map_take, toList_isub hpl]
  | @hcomp k g A t ps u a φ hm hH hsc hn hpl hAeq he ha hu iha ihu =>
    intro k' σ
    by_cases hh : (ival (idEnv k') (φ.subst σ.τ)).holds
    · have he' := EqTm.isubS hW he σ
      have hface : EqTm S k' .one [] ((Tm.hcomp (.data d ps) φ u a).isub σ) ((u.isub σ.up).dinst .one) (A.isub σ) :=
        EqTm.hcompFace ((holds_iff_entails (I.scoped_subst hsc σ.sc)).1 hh) (HasTy.eqR he')
      have hu1 := hu k' σ .one trivial hh
      refine hu1.conv hW (fun k f t t' A e hm => ?_) (hAeq.isub hW σ).symm ((he'.trans hface).symm)
      unfold dataMem at hm ⊢; rwa [← semK_eq hW e]
    · refine DR.hcomp (dataMem_isub hW hΘ f (HasTy.eqL he) hm σ) hH (I.scoped_subst hsc σ.sc) hh
        (isList_subst hpl _ _) (hAeq.isub hW σ) (EqTm.isubS hW he σ) (iha k' σ) (fun k'' σ' r hr hh' => ?_)
      have := hu k'' (σ.comp σ') r hr (by rwa [I_subst_subst] at hh')
      rw [ISub.comp_hom]
      convert this using 1
      · show ((Tm.data d ps).isub σ).isub σ' = _
        exact Tm.isub_isub _ _ _
      · show ((u.isub σ.up).isub σ'.up).dinst r = _
        rw [Tm.isub_isub, ← ISub.up_comp]

end dr

end

end Model.Canon
