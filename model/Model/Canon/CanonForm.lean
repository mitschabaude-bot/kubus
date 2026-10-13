import Model.Canon.Final

/-!
# Canonicity: canonical forms at stage 0

At stage 0 the interval arguments of a constructor are closed, hence `0` or `1`; a constructor
whose boundary holds computes to its boundary (`conBnd`), which is built from recursive arguments
and earlier constructors; a formal composition has an empty face.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig}

/-! ### Closed interval terms -/

/-- The constant value of a closed interval term. -/
def normI (r : I) : I := if r.eval (fun _ => .zero) = .one then .one else .zero

theorem eval_closed_bool {r : I} (hr : r.Scoped 0) (ρ : ℕ → I.M4) : r.eval ρ = .zero ∨ r.eval ρ = .one := by
  induction r with
  | zero => exact .inl rfl
  | one => exact .inr rfl
  | var i => exact absurd hr (Nat.not_lt_zero _)
  | neg r ih =>
    rcases ih hr with h | h <;> simp [I.eval, h] <;> rfl
  | and r s ihr ihs =>
    rcases ihr hr.1 with h1 | h1 <;> rcases ihs hr.2 with h2 | h2 <;> simp [I.eval, h1, h2] <;> rfl
  | or r s ihr ihs =>
    rcases ihr hr.1 with h1 | h1 <;> rcases ihs hr.2 with h2 | h2 <;> simp [I.eval, h1, h2] <;> rfl

theorem normI_const (r : I) : normI r = .zero ∨ normI r = .one := by
  unfold normI; split <;> simp

theorem I_eq_normI {r : I} (hr : r.Scoped 0) : I.Eq r (normI r) := by
  intro ρ
  have he : r.eval ρ = r.eval (fun _ => .zero) := Cof.eval_congr hr (fun n hn => absurd hn (Nat.not_lt_zero _))
  unfold normI
  split
  · rename_i h; rw [he, h]; rfl
  · rename_i h
    rcases eval_closed_bool hr (fun _ => .zero) with h' | h'
    · rw [he, h']; rfl
    · exact absurd h' h

/-! ### Replacing the recursive arguments of a constructor -/

theorem EqTele0.ofList_of' {Ψ : ℕ} {Φ : I} {Γ : Ctx} (hw : Wf0 S Ψ Φ Γ) :
    ∀ (as as' Δ prev : List Tm), as.length = Δ.length → as'.length = Δ.length →
    (∀ (k : ℕ) (a a' A : Tm), as[k]? = some a → as'[k]? = some a' → Δ[k]? = some A →
      EqTm0 S Ψ Φ Γ a a' (A.substList ((as.take k).reverse ++ prev))) →
    EqTele0 S Ψ Φ Γ (Tm.ofList as) (Tm.ofList as') Δ prev
  | [], [], [], _, _, _, _ => .nil hw
  | a :: as, a' :: as', A :: Δ, prev, hl, hl', h => by
    refine .cons (by simpa using h 0 a a' A rfl rfl rfl)
      (EqTele0.ofList_of' hw as as' Δ (a :: prev) (by simpa using hl) (by simpa using hl') ?_)
    intro k b b' B hb hb' hB
    have := h (k + 1) b b' B (by simpa using hb) (by simpa using hb') (by simpa using hB)
    simpa using this
  | [], _ :: _, _, _, hl, hl', _ => by simp at hl hl'; omega
  | _ :: _, [], _, _, hl, hl', _ => by simp at hl hl'; omega
  | [], [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, hl, _, _ => by simp at hl

theorem simpleArgs_isList {ctors : List Ctor} {d np c n : ℕ} {C C' : Ctor} :
    ∀ {k : ℕ} {as : Tm}, Ctor.simpleArgs ctors d np c n C C' k as = true → as = Tm.ofList as.toList
  | _, .tcons a as, h => by
    simp only [Ctor.simpleArgs, Bool.and_eq_true] at h
    simp only [Tm.toList, Tm.ofList]; rw [← simpleArgs_isList h.2]
  | _, .tnil, _ => rfl
  | _, .var _, h | _, .univ _, h | _, .abort, h | _, .const _, h => by simp [Ctor.simpleArgs] at h
  | _, .pi _ _, h | _, .sigma _ _, h | _, .lam _ _, h | _, .app _ _, h | _, .pair _ _, h => by
    simp [Ctor.simpleArgs] at h
  | _, .fst _, h | _, .snd _, h | _, .plam _, h | _, .ipi _, h | _, .papp _ _, h => by
    simp [Ctor.simpleArgs] at h
  | _, .path _ _ _, h | _, .split _ _ _ _, h | _, .transp _ _ _, h | _, .hcomp _ _ _ _, h => by
    simp [Ctor.simpleArgs] at h
  | _, .glue _ _ _ _, h | _, .glueEl _ _ _ _, h | _, .unglue _ _ _, h => by simp [Ctor.simpleArgs] at h
  | _, .data _ _, h | _, .con _ _ _ _ _, h | _, .elim _ _ _ _ _, h => by simp [Ctor.simpleArgs] at h

theorem simpleArgs_rec {ctors : List Ctor} {d np c n : ℕ} {C C' : Ctor} :
    ∀ {k : ℕ} {as : Tm}, Ctor.simpleArgs ctors d np c n C C' k as = true →
    ∀ j (hj : j < as.toList.length), C'.isRec (k + j) = true → Ctor.simpleB ctors d np c n C as.toList[j] = true
  | k, .tcons a as, h, j, hj, hr => by
    simp only [Ctor.simpleArgs, Bool.and_eq_true] at h
    cases j with
    | zero =>
      simp only [Nat.add_zero] at hr
      simp only [Tm.toList, List.getElem_cons_zero]
      have := h.1; rw [if_pos hr] at this; exact this
    | succ j =>
      simp only [Tm.toList, List.getElem_cons_succ]
      exact simpleArgs_rec h.2 j (by simp [Tm.toList] at hj; omega) (by rw [← hr]; congr 1; omega)
  | _, .tnil, _, j, hj, _ => by simp [Tm.toList] at hj
  | _, .var _, h, _, _, _ | _, .univ _, h, _, _, _ | _, .abort, h, _, _, _ | _, .const _, h, _, _, _ => by
    simp [Ctor.simpleArgs] at h
  | _, .pi _ _, h, _, _, _ | _, .sigma _ _, h, _, _, _ | _, .lam _ _, h, _, _, _ | _, .app _ _, h, _, _, _ => by
    simp [Ctor.simpleArgs] at h
  | _, .pair _ _, h, _, _, _ | _, .fst _, h, _, _, _ | _, .snd _, h, _, _, _ | _, .plam _, h, _, _, _ => by
    simp [Ctor.simpleArgs] at h
  | _, .ipi _, h, _, _, _ | _, .papp _ _, h, _, _, _ | _, .path _ _ _, h, _, _, _ => by
    simp [Ctor.simpleArgs] at h
  | _, .split _ _ _ _, h, _, _, _ | _, .transp _ _ _, h, _, _, _ | _, .hcomp _ _ _ _, h, _, _, _ => by
    simp [Ctor.simpleArgs] at h
  | _, .glue _ _ _ _, h, _, _, _ | _, .glueEl _ _ _ _, h, _, _, _ | _, .unglue _ _ _, h, _, _, _ => by
    simp [Ctor.simpleArgs] at h
  | _, .data _ _, h, _, _, _ | _, .con _ _ _ _ _, h, _, _, _ | _, .elim _ _ _ _ _, h, _, _, _ => by
    simp [Ctor.simpleArgs] at h

theorem sizeOf_toList_lt : ∀ {as : Tm} {a : Tm}, a ∈ as.toList → sizeOf a < sizeOf as
  | .tcons x xs, a, h => by
    simp only [Tm.toList, List.mem_cons] at h
    rcases h with rfl | h
    · simp; omega
    · have := sizeOf_toList_lt h; simp; omega
  | .tnil, a, h => by simp [Tm.toList] at h
  | .var _, _, h | .univ _, _, h | .abort, _, h | .const _, _, h => by simp [Tm.toList] at h
  | .pi _ _, _, h | .sigma _ _, _, h | .lam _ _, _, h | .app _ _, _, h | .pair _ _, _, h => by simp [Tm.toList] at h
  | .fst _, _, h | .snd _, _, h | .plam _, _, h | .ipi _, _, h | .papp _ _, _, h => by simp [Tm.toList] at h
  | .path _ _ _, _, h | .split _ _ _ _, _, h | .transp _ _ _, _, h | .hcomp _ _ _ _, _, h => by
    simp [Tm.toList] at h
  | .glue _ _ _ _, _, h | .glueEl _ _ _ _, _, h | .unglue _ _ _, _, h => by simp [Tm.toList] at h
  | .data _ _, _, h | .con _ _ _ _ _, _, h | .elim _ _ _ _ _, _, h => by simp [Tm.toList] at h

variable (hW : WfSig S)
include hW

/-- Recursive arguments do not occur in the types of later point arguments. -/
theorem argTy_point_congr {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {j : ℕ} {A0 : Tm} (hA0 : C.args[j]? = some (.point A0)) {args args' : List Tm}
    (hj : j ≤ args.length) (hj' : j ≤ args'.length) (R : List Tm) (hR : R.length = D.params.length)
    (hpt : ∀ i (hi : i < args.length) (hi' : i < args'.length), C.isRec i = false → args'[i] = args[i]) :
    A0.substList ((args'.take j).reverse ++ R) = A0.substList ((args.take j).reverse ++ R) := by
  obtain ⟨hcl, -, hnr, -⟩ := ((hW.2 d D hD).2.2 c C hC).1 j A0 hA0
  simp only [Tm.substList]
  apply subst_freeIn_congr
  intro y hy
  have hyl := freeIn_lt A0 _ _ _ hcl hy
  by_cases hyj : y < j
  · have hnr' : C.isRec (j - 1 - y) = false := by
      simp only [Ctor.noRecDeps, List.all_eq_true, List.mem_range] at hnr
      have := hnr (j - 1 - y) (by omega)
      rw [show j - 1 - (j - 1 - y) = y by omega, hy] at this
      simpa using this
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_reverse (show y < (args'.take j).length by simp; omega),
      List.getElem?_reverse (show y < (args.take j).length by simp; omega), List.length_take,
      Nat.min_eq_left hj, Nat.min_eq_left hj', List.getElem?_take]
    rw [if_pos (by omega), if_pos (by omega), List.getElem?_eq_getElem (show j - 1 - y < args'.length by omega),
      List.getElem?_eq_getElem (show j - 1 - y < args.length by omega), hpt _ (by omega) (by omega) hnr']
    rfl
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp [Nat.min_eq_left hj, Nat.min_eq_left hj']

omit hW in
theorem argTy_rec_nil {C : Ctor} {j d np : ℕ} (hnp : np = 0) (hr : C.isRec j = true) (L : List Tm) :
    (C.argTy d np j).substList L = .data d .tnil := by
  subst hnp; rw [argTy_rec hr]; rfl

/-- Replacing the recursive arguments of a constructor of a parameterless inductive type by
judgmentally equal ones. -/
theorem replace_rec {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hp : D.params = []) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {args args' : List Tm} (hlen : args'.length = args.length)
    (htele : HasTele0 S 0 .one [] (Tm.ofList args) (C.argTys d D.params.length) [])
    (hrec : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      EqTm0 S 0 .one [] args[j] args'[j] (.data d .tnil))
    (hpt : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false → args'[j] = args[j]) :
    HasTele0 S 0 .one [] (Tm.ofList args') (C.argTys d D.params.length) [] ∧
      EqTele0 S 0 .one [] (Tm.ofList args) (Tm.ofList args') (C.argTys d D.params.length) [] := by
  have hal : args.length = C.args.length := by
    have := tele_length htele; rwa [toList_ofList, argTys_length] at this
  have hw : Wf0 S 0 .one [] := Wf0.nil trivial
  have hnp : D.params.length = 0 := by rw [hp]; rfl
  have key : ∀ j (hj : j < args.length) (hj' : j < args'.length),
      HasTy0 S 0 .one [] args'[j] ((C.argTy d D.params.length j).substList ((args'.take j).reverse ++ [])) ∧
      EqTm0 S 0 .one [] args[j] args'[j] ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ [])) := by
    intro j hj hj'
    have hjC : j < C.args.length := by omega
    have ht := tele_get htele j args[j] _ (by rw [toList_ofList]; exact List.getElem?_eq_getElem hj) (argTys_get hjC)
    rw [toList_ofList] at ht
    cases hr : C.isRec j
    · obtain ⟨A0, hA0⟩ := point_of_not_rec hjC hr
      have hAk : C.argTy d D.params.length j = A0 := by simp [Ctor.argTy, hA0]
      rw [hAk] at ht ⊢
      rw [hpt j hj hj' hr, argTy_point_congr hW hD hC hA0 hj.le hj'.le [] (by simp [hp])
        (fun i hi hi' hri => hpt i hi hi' hri)]
      exact ⟨ht, EqTm0.refl ht⟩
    · rw [argTy_rec_nil hnp hr, argTy_rec_nil hnp hr]
      have e := hrec j hj hj' hr
      exact ⟨spec_to_minimal hW (HasTy.eqR (minimal_to_spec_eq e)), e⟩
  refine ⟨HasTele0.ofList_of hw _ _ _ (by rw [argTys_length]; omega) fun j a A ha hA => ?_,
    EqTele0.ofList_of' hw _ _ _ _ (by rw [argTys_length]; omega) (by rw [argTys_length]; omega)
      fun j a a' A ha ha' hA => ?_⟩
  · have hj' : j < args'.length := (List.getElem?_eq_some_iff.1 ha).1
    obtain ⟨-, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    have hjC : j < C.args.length := by omega
    rw [argTys_get hjC] at hA; obtain rfl := Option.some.inj hA
    exact (key j (by omega) hj').1
  · have hj : j < args.length := (List.getElem?_eq_some_iff.1 ha).1
    obtain ⟨-, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 ha'
    have hjC : j < C.args.length := by omega
    rw [argTys_get hjC] at hA; obtain rfl := Option.some.inj hA
    exact (key j hj hj').2

/-- A constructor of a parameterless inductive type at stage 0 whose recursive arguments have
canonical forms has a canonical form, by induction on the constructor index (the boundary of a
constructor is built from recursive arguments and earlier constructors). -/
theorem canon_con {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hp : D.params = []) :
    ∀ (c : ℕ) (C : Ctor) (args : List Tm) (rs : List I), D.ctors[c]? = some C →
    HasTy S 0 .one [] (.con d c .tnil (Tm.ofList args) rs) (.data d .tnil) →
    (∀ j (hj : j < args.length), C.isRec j = true →
      ∃ t', EqTm S 0 .one [] args[j] t' (.data d .tnil) ∧ Canon S d t') →
    ∃ t', EqTm S 0 .one [] (.con d c .tnil (Tm.ofList args) rs) t' (.data d .tnil) ∧ Canon S d t' := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
  intro C args rs hC hty hrec
  have h0 := spec_to_minimal hW hty
  obtain ⟨hI, -⟩ := gen_conF h0 rfl
  obtain ⟨-, D0, C0, hD0, hC0, -, hdq, hqt, haq, hrs, hrsc⟩ := hI
  rw [hD] at hD0; cases hD0; rw [hC] at hC0; cases hC0
  -- canonical recursive arguments
  let args' : List Tm := List.ofFn (n := args.length) fun j =>
    if h : C.isRec j = true then (hrec j j.2 h).choose else args[j]
  have hl' : args'.length = args.length := by simp [args']
  have hget : ∀ j (hj : j < args.length) (hj' : j < args'.length),
      args'[j] = if h : C.isRec j = true then (hrec j hj h).choose else args[j] := by
    intro j hj hj'; simp [args']
  obtain ⟨htele', eqt⟩ := replace_rec hW hD hp hC hl' haq
    (fun j hj hj' hr => by rw [hget j hj hj', dif_pos hr]; exact spec_to_minimal_eq hW (hrec j hj hr).choose_spec.1)
    (fun j hj hj' hr => by rw [hget j hj hj', dif_neg (by simp [hr])])
  have hcanrec : ∀ j (hj : j < args'.length), C.isRec j = true → Canon S d args'[j] := by
    intro j hj hr
    rw [hget j (by omega) hj, dif_pos hr]; exact (hrec j (by omega) hr).choose_spec.2
  have hcon' := HasTy0.con hD hC rfl hdq hqt htele' hrs hrsc
  have e1 := EqTm0.con hD hC h0 hcon' (EqTele0.refl hqt) eqt rfl
    (fun k r r' h1 h2 => by rw [h1] at h2; cases h2; exact I_eq_refl _)
  -- constant interval arguments
  let rs' := rs.map normI
  have hrs' : rs'.length = C.dims := by simp [rs', hrs]
  have hsc' : ∀ r ∈ rs', r.Scoped 0 := by
    intro r hr; obtain ⟨r0, -, rfl⟩ := List.mem_map.1 hr
    rcases normI_const r0 with h | h <;> rw [h] <;> trivial
  have hcon'' := HasTy0.con hD hC rfl hdq hqt htele' hrs' hsc'
  have e2 := EqTm0.con hD hC hcon' hcon'' (EqTele0.refl hqt) (EqTele0.refl htele') (by simp [rs'])
    (fun k r r' h1 h2 => by
      simp only [rs', List.getElem?_map, h1, Option.map_some, Option.some.injEq] at h2
      subst h2; exact I_eq_normI (hrsc r (List.mem_of_getElem? h1)))
  have hconst : ∀ r ∈ rs', r = .zero ∨ r = .one := by
    intro r hr; obtain ⟨r0, -, rfl⟩ := List.mem_map.1 hr; exact normI_const r0
  have e12 := minimal_to_spec_eq (EqTm0.trans e1 e2)
  by_cases hb : ∃ (k : ℕ) (ψ : I) (b : Tm), C.bnd[k]? = some (ψ, b) ∧ I.Entails .one (Ctor.cofAt ψ rs')
  · obtain ⟨k, ψ, b, hk, hent⟩ := hb
    have e3 := EqTm.conBnd hD hC hk hent (show Tm.tnil = Tm.ofList Tm.tnil.toList from rfl)
      (show Tm.ofList args' = Tm.ofList (Tm.ofList args').toList by rw [toList_ofList]) (minimal_to_spec hcon'')
    rw [toList_ofList] at e3
    obtain ⟨-, -, hsimple, -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 k ψ b hk
    have hnp : D.params.length = 0 := by rw [hp]; rfl
    rw [hnp] at hsimple
    -- the boundary is canonical, by recursion on its (simple) structure
    have canon_bnd : ∀ N (b : Tm), sizeOf b < N → Ctor.simpleB D.ctors d 0 c C.args.length C b = true →
        HasTy S 0 .one [] (Ctor.bndAt b [] args' rs') (.data d .tnil) →
        ∃ t', EqTm S 0 .one [] (Ctor.bndAt b [] args' rs') t' (.data d .tnil) ∧ Canon S d t' := by
      intro N
      induction N with
      | zero => intro b hb; omega
      | succ N ihN =>
        intro b hsb hsim htyb
        match b, hsim with
        | .var j, hsim =>
          simp only [Ctor.simpleB, Bool.and_eq_true, decide_eq_true_eq] at hsim
          obtain ⟨hjn, hjr⟩ := hsim
          refine ⟨_, EqTm.refl htyb, ?_⟩
          have hn : args'.length = C.args.length := by
            have := tele_length htele'; rwa [toList_ofList, argTys_length] at this
          have hbv : Ctor.bndAt (.var j) [] args' rs' = args'[C.args.length - 1 - j]'(by omega) := by
            show (args'.reverse ++ ([] : List Tm).reverse).getD j (.var j) = _
            rw [List.reverse_nil, List.append_nil, List.getD_eq_getElem?_getD,
              List.getElem?_reverse (show j < args'.length by omega), List.getElem?_eq_getElem (by omega)]
            simp [hn]
          rw [hbv]
          exact hcanrec _ (by omega) hjr
        | .con d' c' ps'' as rs'', hsim =>
          simp only [Ctor.simpleB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsim
          obtain ⟨⟨⟨hdd, hc'⟩, hps⟩, hmatch⟩ := hsim
          subst d'
          subst ps''
          cases hC' : D.ctors[c']? with
          | none => rw [hC'] at hmatch; exact absurd hmatch (by simp)
          | some C' =>
            rw [hC'] at hmatch
            simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
            obtain ⟨⟨-, -⟩, hargs⟩ := hmatch
            have hasl := simpleArgs_isList hargs
            let σb : ℕ → Tm := fun j => (args'.reverse ++ ([] : List Tm).reverse).getD j (.var j)
            let τb : ℕ → I := fun i => rs'.reverse.getD i (.var i)
            have hbe : Ctor.bndAt (.con d c' (Ctor.paramVars 0 C.args.length) as rs'') [] args' rs' =
                .con d c' .tnil (Tm.ofList (as.toList.map (·.subst σb τb))) (rs''.map (·.subst τb)) := by
              show Tm.con d c' ((Ctor.paramVars 0 C.args.length).subst σb τb) (as.subst σb τb) (rs''.map (·.subst τb)) = _
              congr 1
              rw [hasl, ofList_subst, toList_ofList]
            rw [hbe] at htyb ⊢
            refine ihc c' hc' C' _ _ hC' htyb fun j hj hr => ?_
            have hj0 : j < as.toList.length := by simpa using hj
            have hsimj := simpleArgs_rec hargs j hj0 (by simpa using hr)
            have hsz : sizeOf (as.toList[j]) < N := by
              have h1 := sizeOf_toList_lt (List.getElem_mem hj0)
              have h2 : sizeOf as < sizeOf (Tm.con d c' (Ctor.paramVars 0 C.args.length) as rs'') := by
                simp; omega
              omega
            -- the typing of the recursive argument
            obtain ⟨hI', -⟩ := gen_conF (spec_to_minimal hW htyb) rfl
            obtain ⟨-, D1, C1, hD1, hC1, -, -, -, haq', -, -⟩ := hI'
            rw [hD] at hD1; cases hD1; rw [hC'] at hC1; cases hC1
            have hjC : j < C'.args.length := by
              have := tele_length haq'; rw [toList_ofList, argTys_length] at this; omega
            have hjt := tele_get haq' j _ _ (by rw [toList_ofList]; exact List.getElem?_eq_getElem hj) (argTys_get hjC)
            rw [argTy_rec_nil hnp hr] at hjt
            have := ihN (as.toList[j]) hsz hsimj (by
              rw [List.getElem_map] at hjt
              exact minimal_to_spec hjt)
            simpa [List.getElem_map] using this
    obtain ⟨t', eb, hcan⟩ := canon_bnd (sizeOf b + 1) b (Nat.lt_succ_self _) hsimple (HasTy.eqR e3)
    exact ⟨t', EqTm.trans e12 (EqTm.trans e3 eb), hcan⟩
  · refine ⟨_, e12, Canon.con hD hC hconst (fun ψ b hψb hent => hb ?_) hcanrec (minimal_to_spec hcon'')⟩
    obtain ⟨k, hk, heq⟩ := List.getElem_of_mem hψb
    exact ⟨k, ψ, b, by rw [List.getElem?_eq_getElem hk, heq], hent⟩

omit hW in
theorem ent_of_ieq {φ ψ : I} (h : I.Eq φ ψ) : I.Entails φ ψ := entails_iff.2 fun ρ _ hφ => by rw [← h ρ]; exact hφ

omit hW in
/-- A closed face that does not hold is empty. -/
theorem ieq_zero_of_not_holds {φ : I} (hφ : φ.Scoped 0) (hn : ¬ (ival (idEnv 0) φ).holds) : I.Eq φ .zero := by
  have h := I_eq_normI hφ
  rcases normI_const φ with h' | h'
  · rw [h'] at h; exact h
  · rw [h'] at h
    exact absurd ((holds_iff_entails hφ).2 (ent_of_ieq (I_eq_symm h))) hn

/-- The computable elements of a parameterless inductive type at stage 0 have canonical forms. -/
theorem canon_of_DR {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hp : D.params = []) :
    ∀ {k : ℕ} {g : Hom k 0} {A t : Tm},
      DR S d D (dataMem S (ΘK S D d 0 .tnil) (Hom.id 0)) (dataP S (ΘK S D d 0 .tnil) (Hom.id 0)) k g A t →
      k = 0 → TyEq S k A (.data d .tnil) → ∃ t', EqTm S k .one [] t t' (.data d .tnil) ∧ Canon S d t' := by
  have hS := sigClosed_of_wfSig hW
  have hnil : ∀ {qs : Tm} {l : ℕ}, HasTy S 0 .one [] (.data d qs) (.univ l) → qs = .tnil := by
    intro qs l h
    obtain ⟨D', hD', ht⟩ := gen_data_tele (spec_to_minimal hW h) rfl
    rw [hD] at hD'; cases hD'
    have h1 := tele_isList ht
    have h2 := tele_length ht
    rw [hp] at h2
    rw [h1, List.eq_nil_of_length_eq_zero h2]; rfl
  have hdT : HasTy S 0 .one [] (.data d .tnil) (.univ D.level) := minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1
    (by rw [hp]; exact HasTele0.nil (Ψ := 0) (Φ := .one) (Γ := []) (Wf0.nil trivial)))
  intro k g A t h
  induction h with
  | @con k g A t qs c C args rs hm hC hrs hsc hqs hAeq he hlen hrec hpt ihrec =>
    intro hk hA
    subst hk
    have hqp : TyEq S 0 (.data d qs) (.data d .tnil) := hAeq.symm.trans hW hA
    obtain ⟨lq, eq⟩ := tyEq_eq hW hqp ⟨_, hdT⟩
    have hq := hnil (HasTy.eqL eq)
    subst hq
    have htc := he.tyConv hA
    obtain ⟨t', e, hcan⟩ := canon_con hW hD hp c C args rs hC (HasTy.eqR htc)
      (fun j hj hr => ihrec j hj hr rfl (TyEq.refl _))
    exact ⟨t', EqTm.trans htc e, hcan⟩
  | @hcomp k g A t qs u a φ hm hH hsc hn hqs hAeq he ha hu iha ihu =>
    intro hk hA
    subst hk
    have hqp : TyEq S 0 (.data d qs) (.data d .tnil) := hAeq.symm.trans hW hA
    obtain ⟨lq, eq⟩ := tyEq_eq hW hqp ⟨_, hdT⟩
    have hq := hnil (HasTy.eqL eq)
    subst hq
    have htc := he.tyConv hA
    obtain ⟨a', ea, hcan⟩ := iha rfl (TyEq.refl _)
    have hz := ieq_zero_of_not_holds hsc hn
    have hh := spec_to_minimal hW (HasTy.eqR htc)
    obtain ⟨l0, ⟨hAt, -, hut, hat, -⟩, -⟩ := gen_hcomp hh rfl
    have hentz : I.Entails (cof .one φ) .zero := ent_trans (ent_and_right _ _) (ent_of_ieq hz)
    have ha't := spec_to_minimal hW (HasTy.eqR ea)
    have hXs : (cof I.one I.zero).Scoped 0 := ⟨trivial, trivial⟩
    have hh' : HasTy0 S 0 .one [] (.hcomp (.data d .tnil) .zero a'.dshift a') (.data d .tnil) :=
      HasTy0.hcomp hAt trivial
        (HasTy0.restrict (scoped_shift hXs) (ent_shift (ent_and_left _ _)) (HasTy0.dwk hS ha't)) ha't
        (EqTm0.absurd (ent_and_right _ _)
          (by rw [dshift_dinst]; exact HasTy0.restrict hXs (ent_and_left _ _) ha't)
          (HasTy0.restrict hXs (ent_and_left _ _) ha't))
    have hXφ : (cof I.one φ).Scoped 0 := ⟨trivial, hsc⟩
    have eqh := EqTm0.hcomp hh hh' (EqTm0.refl hAt) (ent_of_ieq hz) (ent_of_ieq (I_eq_symm hz))
      (EqTm0.absurd (ent_shift hentz) hut
        (HasTy0.restrict (scoped_shift hXφ) (ent_shift (ent_and_left _ _)) (HasTy0.dwk hS ha't)))
      (spec_to_minimal_eq hW ea)
    exact ⟨_, EqTm.trans htc (minimal_to_spec_eq eqh), Canon.hcomp hD hH hcan⟩

end


/-- **Canonicity** (assuming the compatibility of Glue annotations, `GlueCompat`): a closed
element of a parameterless inductive type is judgmentally equal to a canonical form. -/
theorem canonicity_of_glueCompat : ∀ (S : Sig) (d : Nat) (D : DataDecl) (t : Tm), WfSig S → GlueCompat S →
    S[d]? = some (.data D) → D.params = [] → HasTy S 0 .one [] t (.data d .tnil) →
    ∃ t', EqTm S 0 .one [] t t' (.data d .tnil) ∧ Canon S d t' := by
  intro S d D t hW hG hD hp ht
  have hc : t.ConstsLt S.length := (sound_ty (sigOK_of_wfSig _ S rfl hW) ht).2.1
  have hRE := fund_ty hW (hyp_all hW hG S.length le_rfl) hG (spec_to_minimal hW ht) hc 0 (CSub.nil S 0)
  have htc := closed_of_ty hW ht
  rw [closed_subst_id htc (fun x hx => absurd hx (Nat.not_lt_zero _)) (fun i hi => absurd hi (Nat.not_lt_zero _))] at hRE
  have hdT : HasTy S 0 .one [] (.data d .tnil) (.univ D.level) := minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1
    (by rw [hp]; exact HasTele0.nil (Ψ := 0) (Φ := .one) (Γ := []) (Wf0.nil trivial)))
  obtain ⟨-, hdr⟩ := (RE_data_iff hW hD hdT).1 hRE
  exact canon_of_DR hW hD hp hdr rfl (TyEq.refl _)

end Model.Canon
