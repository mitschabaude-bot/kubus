import Model.Whnf.Kan2DataHITConRel
import Model.Whnf.NearAll

/-!
# Computable simple constructor trees

Tree leaves stand for opaque closing terms. Recursive leaves carry their relation at the data type; point leaves stay literal variables and carry the relation at the constructor's instantiated argument type. This records the information needed to interpret boundary normalization using the relation of earlier constructors.
-/

set_option autoImplicit false

namespace Model.Whnf.Boundary2

open KubusCore KubusCore.Meta Model.Canon Model.Whnf

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k d N : ℕ} {D : DataDecl} {P : Tm}

def close (d : ℕ) (P : Tm) (γ : ℕ → Tm) (τ : ℕ → I) : Tm → Tm :=
  KubusCore.Boundary.eval (fun c as rs => .con d c P (Tm.ofList as) rs) γ τ

def closeArgs (d : ℕ) (P : Tm) (γ : ℕ → Tm) (τ : ℕ → I) : Tm → List Tm :=
  KubusCore.Boundary.evalArgs (fun c as rs => .con d c P (Tm.ofList as) rs) γ τ

theorem closeArgs_ofList (γ : ℕ → Tm) (τ : ℕ → I) (as : List Tm) :
    closeArgs d P γ τ (Tm.ofList as) = as.map (close d P γ τ) := by
  induction as <;> simp_all [closeArgs, close, Tm.ofList, KubusCore.Boundary.evalArgs]

abbrev argAt (d : ℕ) (D : DataDecl) (P : Tm) (C : Ctor) (as : List Tm) (i : ℕ) : Tm :=
  (C.argTy d D.params.length i).substList ((as.take i).reverse ++ P.toList.reverse)

inductive Comp (S : Sig) (k d : ℕ) (D : DataDecl) (P : Tm) (N : ℕ) (γ : ℕ → Tm) (τ : ℕ → I) : Tm → Prop
  | var (j : ℕ) : RE2 S k (.data d P) (γ j) (γ j) → Comp S k d D P N γ τ (.var j)
  | con {d' c : ℕ} {ps as : Tm} {rs : List I} {C : Ctor} :
      c < N → D.ctors[c]? = some C → as = Tm.ofList as.toList → as.toList.length = C.args.length →
      HasTy S k .one [] (close d P γ τ (.con d' c ps as rs)) (.data d P) →
      (∀ i (hi : i < as.toList.length), C.isRec i = true → Comp S k d D P N γ τ as.toList[i]) →
      (∀ i (hi : i < as.toList.length), C.isRec i = false → ∃ j, as.toList[i] = .var j ∧
        RE2 S k (argAt d D P C (closeArgs d P γ τ as) i) (γ j) (γ j)) →
      Comp S k d D P N γ τ (.con d' c ps as rs)

theorem Comp.typed {γ : ℕ → Tm} {τ : ℕ → I} {t : Tm} (h : Comp S k d D P N γ τ t) :
    HasTy S k .one [] (close d P γ τ t) (.data d P) := by
  cases h with
  | var j h => exact (RE2.typed h).1
  | con _ _ _ _ ht _ _ => exact ht

theorem inear_subst (τ : ℕ → I) : ∀ {rs ss : List I}, KubusCore.Boundary.INear rs ss →
    IEqL (rs.map (·.subst τ)) (ss.map (·.subst τ))
  | [], [], _ => .nil
  | [], _ :: _, h | _ :: _, [], h => False.elim h
  | _ :: _, _ :: _, h => .cons (I_eq_subst h.1 τ) (inear_subst τ h.2)

theorem near_close (γ : ℕ → Tm) (τ : ℕ → I) : ∀ (t u : Tm), KubusCore.Boundary.Near t u →
    TmNear (close d P γ τ t) (close d P γ τ u) ∧
      NearL (closeArgs d P γ τ t) (closeArgs d P γ τ u) := by
  intro t
  induction t with
  | var x =>
    intro u h; cases u <;> simp only [KubusCore.Boundary.Near] at h
    subst h; exact ⟨TmNear.refl _, .nil⟩
  | tnil =>
    intro u h; cases u <;> simp only [KubusCore.Boundary.Near] at h
    exact ⟨.abort, .nil⟩
  | tcons a as iha ihas =>
    intro u h; cases u <;> simp only [KubusCore.Boundary.Near] at h
    exact ⟨.abort, .cons (iha _ h.1).1 (ihas _ h.2).2⟩
  | con d' c ps as rs _ ihas =>
    intro u h; cases u <;> simp only [KubusCore.Boundary.Near] at h
    obtain ⟨rfl, rfl, rfl, ha, hrs⟩ := h
    exact ⟨.con (TmNear.refl _) (ofList_near (ihas _ ha).2) (inear_subst τ hrs), .nil⟩
  | _ => intro u h; cases u <;> cases h

section rel

variable (hW : WfSig S) (hD : S[d]? = some (.data D))
  (hP : HasTy S k .one [] (.data d P) (.univ D.level)) (hPP : RT2 S k (.data d P) (.data d P))
  (ih : ∀ c < N, CRSt S d D k P c)
include hW hD hP hPP ih

omit hD hPP ih in
theorem p_id : P.isub (ISub.id k) = P := by
  apply isub_id_of_closed
  have := closed_of_ty hW hP
  simpa [Tm.closedB] using this

omit ih in
theorem p_lit : P = Tm.ofList P.toList := by
  have h := (dataLit_rel hW hD hP hPP (ISub.id k)).2.2.2.2.2.1
  rwa [p_id hW hP] at h

omit hPP ih in
theorem p_len : P.toList.length = D.params.length := by
  have := data_len_of hW (⟨_, .inl hP⟩ : IsTyK S k (.data d P))
  rwa [dataD_eq hW hD] at this

omit hD hPP in
theorem lower_con {c : ℕ} {C : Ctor} (hc : c < N) (hC : D.ctors[c]? = some C)
    {X X' : List Tm} {rs rs' : List I}
    (ht : HasTy S k .one [] (.con d c P (Tm.ofList X) rs) (.data d P))
    (ht' : HasTy S k .one [] (.con d c P (Tm.ofList X') rs') (.data d P))
    (hrs : List.Forall₂ I.Eq rs rs')
    (ha : ∀ i (_hi : i < C.args.length), RE2 S k (argAt d D P C X i) (X.getD i .abort) (X'.getD i .abort)) :
    RE2 S k (.data d P) (.con d c P (Tm.ofList X) rs) (.con d c P (Tm.ofList X') rs') := by
  have hid := p_id hW hP
  have h := ih c hc (ISub.id k) hC (by simpa only [hid] using ht) (by simpa only [hid] using ht') hrs
    (by simpa only [hid] using ha)
  simpa only [hid] using h

theorem Comp.diag {γ : ℕ → Tm} {τ : ℕ → I} {t : Tm} (h : Comp S k d D P N γ τ t) :
    RE2 S k (.data d P) (close d P γ τ t) (close d P γ τ t) := by
  induction h with
  | var j h => exact h
  | @con d' c ps as rs C hc hC has hal ht hr hp ihr =>
    have el : closeArgs d P γ τ as = as.toList.map (close d P γ τ) := by
      conv_lhs => rw [has]
      exact closeArgs_ofList γ τ _
    apply lower_con hW hP ih hc hC ht ht (forall2_ieq_refl _)
    intro i hi
    have hai : i < as.toList.length := by omega
    change RE2 S k (argAt d D P C (closeArgs d P γ τ as) i)
      ((closeArgs d P γ τ as).getD i .abort) ((closeArgs d P γ τ as).getD i .abort)
    simp only [el, getD_eq_get' (show i < (as.toList.map (close d P γ τ)).length by simp; omega),
      List.getElem_map]
    cases hri : C.isRec i
    · obtain ⟨j, hj, hjR⟩ := hp i hai hri
      simpa only [argAt, el, hj, close, KubusCore.Boundary.eval] using hjR
    · simp only [argAt]
      rw [argTy_rec_inst hri (p_lit hW hD hP hPP) (p_len hW hD hP) (by simp; omega)]
      exact ihr i hai hri

theorem Comp.near {γ : ℕ → Tm} {τ : ℕ → I} {t u : Tm} (ht : Comp S k d D P N γ τ t)
    (hn : KubusCore.Boundary.Near t u) (hu : HasTy S k .one [] (close d P γ τ u) (.data d P)) :
    RE2 S k (.data d P) (close d P γ τ t) (close d P γ τ u) :=
  RE2_near hW hPP (ht.diag hW hD hP hPP ih) (near_close γ τ t u hn).1 hu

omit ih in
theorem args_type {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {X Y : List Tm}
    (hX : X.length = C.args.length) (hY : Y.length = C.args.length)
    (ha : ∀ i (_hi : i < C.args.length), RE2 S k (argAt d D P C X i) (X.getD i .abort) (Y.getD i .abort))
    (i : ℕ) (hi : i < C.args.length) : RT2 S k (argAt d D P C X i) (argAt d D P C Y i) := by
  apply argTy_rt2' hW hD hP hPP hPP hC hi (A := X.take i) (B := Y.take i) (by simp; omega) (by simp; omega)
  intro j hj
  rw [List.take_take, Nat.min_eq_left hj.le, getD_take_lt hj, getD_take_lt hj]
  exact ha j (by omega)

omit ih in
theorem con_typed {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {X Y : List Tm} {rs : List I}
    (ht : HasTy S k .one [] (.con d c P (Tm.ofList X) rs) (.data d P))
    (hY : Y.length = C.args.length)
    (ha : ∀ i (_hi : i < C.args.length), RE2 S k (argAt d D P C X i) (X.getD i .abort) (Y.getD i .abort)) :
    HasTy S k .one [] (.con d c P (Tm.ofList Y) rs) (.data d P) := by
  have CI := con_inv hW hD hC ht hP
  have hX : X.length = C.args.length := CI.2.2.2.2.2.1
  have htel : HasTele0 S k .one [] (Tm.ofList Y) (C.argTys d D.params.length) P.toList.reverse := by
    apply HasTele0.ofList_of (show Wf0 S k .one [] from .nil trivial) Y _ _ (by simp [hY, Ctor.argTys])
    intro i a A ha' hA
    have hi : i < C.args.length := by have := (List.getElem?_eq_some_iff.1 ha').1; omega
    have hAT := argTys_get (d := d) (np := D.params.length) hi
    rw [hAT] at hA; cases hA
    have R := RE2.conv hW (args_type hW hD hP hPP hC hX hY ha i hi) (ha i hi)
    have hh := (RE2.typed R).2.1
    rw [List.getD_eq_getElem?_getD, ha'] at hh
    exact spec_to_minimal hW hh
  exact .con hD hC (p_lit hW hD hP hPP) hP (toFull_tele htel) CI.2.2.2.1 CI.2.2.2.2.1

end rel

end

end Model.Whnf.Boundary2
