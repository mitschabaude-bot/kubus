import Model.Boundary
import Model.Whnf.Boundary2Tree

/-!
# Boundary normal forms in the free constructor algebra

Opaque variables are interpreted by distinct constant tags. At a normal constructor, the algebra records its constructor, arguments and interval arguments, so equality of these values reflects equality of normal trees up to `I.Eq`.
-/

set_option autoImplicit false

namespace Model.Whnf.Boundary2

open ZFSet KubusCore KubusCore.Meta Model.Canon Model.Whnf

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k d : ℕ} {D : DataDecl}

inductive NF (ctors : List Ctor) (d : ℕ) (ps : Tm) (k : ℕ) : Tm → Prop
  | var (j : ℕ) : NF ctors d ps k (.var j)
  | con (c : ℕ) (as : List Tm) (rs : List I) :
      (∀ a ∈ as, NF ctors d ps k a) → (∀ r ∈ rs, r.Scoped k) →
      (ctors.getD c default).bnd.find? (fun p => I.entails .one (p.1.subst fun i => rs.reverse.getD i .zero)) = none →
      NF ctors d ps k (.con d c ps (Tm.ofList as) rs)

def marker (k j : ℕ) : V := mkKV k fun _ _ => tagZ 100 (natZ j)

theorem marker_kv (k j : ℕ) : IsKV k (marker k j) := isKV_mkKV _

theorem marker_inj {i j : ℕ} (h : marker k i = marker k j) : i = j := by
  have he := congrArg (here k) h
  simpa [marker, here_mkKV] using he

theorem subst_scoped_all (τ : ℕ → I) (hτ : ∀ i, (τ i).Scoped k) (r : I) : (r.subst τ).Scoped k := by
  induction r <;> simp_all [I.subst, I.Scoped]

theorem head_none {ctors : List Ctor} {c : ℕ} {rs : List I} (hrs : ∀ r ∈ rs, r.Scoped k)
    (hn : (ctors.getD c default).bnd.find?
      (fun p => I.entails .one (p.1.subst fun i => rs.reverse.getD i .zero)) = none) :
    bndAtMap (ctors.getD c default) (rs.map (ival (idEnv k))) (Hom.id k) = none := by
  apply List.find?_eq_none.2
  intro p hp hh
  have hhold : (ival (renv (rs.map (ival (idEnv k)))) p.1).holds := by
    simpa only [decide_eq_true_eq, DM.restr_id] using hh
  have hτ : ∀ i, (rs.reverse.getD i .zero).Scoped k := by
    intro i
    simp only [List.getD_eq_getElem?_getD]
    cases h : rs.reverse[i]? with
    | none => trivial
    | some r => exact hrs r (List.mem_reverse.1 (List.mem_of_getElem? h))
  have hv : (ival (idEnv k) (p.1.subst fun i => rs.reverse.getD i .zero)).holds := by
    rwa [ival.subst, Model.Boundary.dims_env]
  exact (List.find?_eq_none.1 hn p hp) ((holds_iff_entails (subst_scoped_all _ hτ _)).1 hv)

theorem marker_ne_con {ctors : List Ctor} {c j : ℕ} {as : List V} {rs : List (DM k)}
    (hn : bndAtMap (ctors.getD c default) rs (Hom.id k) = none) : marker k j ≠ conV ctors k c as rs := by
  intro he
  have h := congrArg (here k) he
  rw [marker, here_mkKV, here_conV hn, tagZ_inj] at h
  exact (by decide : (100 : ℕ) ≠ Model.tCon) h.1

theorem ival_id_inj {r s : I} (hr : r.Scoped k) (hs : s.Scoped k)
    (h : ival (idEnv k) r = ival (idEnv k) s) : I.Eq r s := by
  intro ρ
  let p : Pt k := fun j => ρ (k - 1 - j)
  have he := congrArg (fun x : DM k => x.fn p) h
  change (ival (idEnv k) r).fn p = (ival (idEnv k) s).fn p at he
  rw [ival_idEnv_fn, ival_idEnv_fn] at he
  have ec : ∀ t : I, t.Scoped k → t.eval (Pt.rev p) = t.eval ρ := by
    intro t ht
    apply Cof.eval_congr ht
    intro i hi
    simp only [Pt.rev, dif_pos hi, p]
    congr 1; omega
  rwa [ec r hr, ec s hs] at he

theorem inear_of_ival : ∀ {rs ss : List I}, (∀ r ∈ rs, r.Scoped k) → (∀ s ∈ ss, s.Scoped k) →
    rs.map (ival (idEnv k)) = ss.map (ival (idEnv k)) → KubusCore.Boundary.INear rs ss
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by cases h
  | r :: rs, s :: ss, hr, hs, h => by
    obtain ⟨he, htail⟩ := List.cons.inj h
    exact ⟨ival_id_inj (hr r (List.mem_cons_self ..)) (hs s (List.mem_cons_self ..)) he,
      inear_of_ival (fun r h => hr r (List.mem_cons_of_mem _ h))
        (fun s h => hs s (List.mem_cons_of_mem _ h)) htail⟩

def denote (ctors : List Ctor) (k : ℕ) : Tm → V :=
  Model.Boundary.read (conV ctors k) (marker k) (idEnv k)

theorem denote_kv (ctors : List Ctor) (k : ℕ) (t : Tm) : IsKV k (denote ctors k t) :=
  Model.Boundary.read_kv (fun c as rs => isKV_conV ctors c as rs) (marker_kv k) _ _

theorem nf_reads {ctors : List Ctor} {ps : Tm} {as : List Tm}
    (ih : ∀ a ∈ as, ∀ b, NF ctors d ps k b → denote ctors k a = denote ctors k b → KubusCore.Boundary.Near a b) :
    ∀ bs, (∀ b ∈ bs, NF ctors d ps k b) → as.map (denote ctors k) = bs.map (denote ctors k) →
      KubusCore.Boundary.Near (Tm.ofList as) (Tm.ofList bs) := by
  induction as with
  | nil => intro bs _ he; cases bs <;> simp_all [Tm.ofList, KubusCore.Boundary.Near]
  | cons a as iht =>
    intro bs hb he
    cases bs with
    | nil => cases he
    | cons b bs =>
      obtain ⟨heh, het⟩ := List.cons.inj he
      exact ⟨ih a (List.mem_cons_self ..) b (hb b (List.mem_cons_self ..)) heh,
        iht (fun a ha => ih a (List.mem_cons_of_mem _ ha)) bs
          (fun b hb' => hb b (List.mem_cons_of_mem _ hb')) het⟩

theorem NF.reflect {ctors : List Ctor} {ps : Tm} {t u : Tm} (ht : NF ctors d ps k t) (hu : NF ctors d ps k u)
    (he : denote ctors k t = denote ctors k u) : KubusCore.Boundary.Near t u := by
  induction ht generalizing u with
  | var j =>
    cases hu with
    | var l => exact marker_inj he
    | con c bs ss hb hss hn =>
      exact False.elim (marker_ne_con (head_none hss hn) he)
  | con c as rs ha hrs hn ih =>
    cases hu with
    | var j => exact False.elim (marker_ne_con (head_none hrs hn) he.symm)
    | con c' bs ss hb hss hn' =>
      change conV ctors k c (Model.Boundary.readArgs (conV ctors k) (marker k) (idEnv k) (Tm.ofList as))
          (rs.map (ival (idEnv k))) =
        conV ctors k c' (Model.Boundary.readArgs (conV ctors k) (marker k) (idEnv k) (Tm.ofList bs))
          (ss.map (ival (idEnv k))) at he
      rw [Model.Boundary.read_ofList, Model.Boundary.read_ofList] at he
      obtain ⟨rfl, hargs, hiss⟩ := conV_inj (head_none hrs hn) (head_none hss hn')
        (fun a ha => by obtain ⟨t, _, rfl⟩ := List.mem_map.1 ha; exact denote_kv ctors k t)
        (fun a ha => by obtain ⟨t, _, rfl⟩ := List.mem_map.1 ha; exact denote_kv ctors k t) he
      exact ⟨rfl, rfl, rfl, nf_reads ih bs hb hargs, inear_of_ival hrs hss hiss⟩

theorem checks (hW : WfSig S) (hD : S[d]? = some (.data D)) :
    ∀ c C, D.ctors[c]? = some C → ∀ ψ b ψ' b', (ψ, b) ∈ C.bnd → (ψ', b') ∈ C.bnd →
      KubusCore.Boundary.Agree D.ctors d D.params.length C.args.length c (.and ψ ψ') b b' := by
  intro c C hC ψ b ψ' b' hb hb'
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hb
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hb'
  exact ((hW.2 d D hD).2.2 c C hC).2.2 i j ψ ψ' b b' hi hj

theorem all_con_sound (hW : WfSig S) (hD : S[d]? = some (.data D)) :
    ∀ c ps, Model.Boundary.ConSound D.ctors d ps c := by
  have ho := Model.Boundary.raw_ovl D.ctors d D.params.length (checks hW hD)
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih => exact fun ps => Model.Boundary.con_sound (ho c) (fun c' hc' => ih c' hc' ps)

theorem agree_read (hW : WfSig S) (hD : S[d]? = some (.data D)) {np nargs c : ℕ} {φ : I} {b b' : Tm}
    (ha : KubusCore.Boundary.Agree D.ctors d np nargs c φ b b')
    (γ : ℕ → V) (hγ : ∀ j, IsKV k (γ j)) (ρ : IEnv k) (hh : (ival ρ φ).holds) :
    Model.Boundary.read (conBefore D.ctors c k) γ ρ b =
      Model.Boundary.read (conBefore D.ctors c k) γ ρ b' := by
  let F := conV D.ctors k
  obtain ⟨α, hα, hρα⟩ := Model.Boundary.holding_face hh
  have hH : ∀ c' xs ss,
      Model.Boundary.read F γ ρ
        (if c' < c then KubusCore.Boundary.conNF D.ctors d (Ctor.paramVars np nargs) c' xs ss else .abort) =
      conBefore D.ctors c k c' (xs.map (Model.Boundary.read F γ ρ)) (ss.map (ival ρ)) := by
    intro c' xs ss
    by_cases hc' : c' < c
    · simp only [hc', ↓reduceIte, conBefore, ↓reduceDIte]
      exact all_con_sound hW hD c' _ k γ ρ hγ xs ss
    · simp [hc', conBefore, Model.Boundary.read, F]
  have hnf : ∀ t, Model.Boundary.read F γ ρ (KubusCore.Boundary.nf D.ctors d np nargs c α t) =
      Model.Boundary.read (conBefore D.ctors c k) γ ρ t := by
    intro t
    have he := (Model.Boundary.read_eval F (conBefore D.ctors c k) γ ρ _ hH
      Tm.var (KubusCore.Boundary.faceSub α) t).1
    change Model.Boundary.read F γ ρ (KubusCore.Boundary.nf D.ctors d np nargs c α t) = _ at he
    rw [Model.Boundary.face_sub_env ρ α hρα] at he
    exact he
  rw [← hnf b, ← hnf b']
  exact (Model.Boundary.read_near F γ ρ _ _ (ha α hα)).1

def norm (ctors : List Ctor) (d : ℕ) (ps : Tm) (c : ℕ) (rs : List I) (b : Tm) : Tm :=
  KubusCore.Boundary.eval
    (fun c' xs ss => if c' < c then KubusCore.Boundary.conNF ctors d ps c' xs ss else .abort)
    Tm.var (fun i => rs.reverse.getD i .zero) b

theorem denote_norm (hW : WfSig S) (hD : S[d]? = some (.data D)) (ps : Tm) (c : ℕ) (rs : List I) (b : Tm) :
    denote D.ctors k (norm D.ctors d ps c rs b) =
      Model.Boundary.read (conBefore D.ctors c k) (marker k) (renv (rs.map (ival (idEnv k)))) b := by
  have hH : ∀ c' xs ss,
      Model.Boundary.read (conV D.ctors k) (marker k) (idEnv k)
        (if c' < c then KubusCore.Boundary.conNF D.ctors d ps c' xs ss else .abort) =
      conBefore D.ctors c k c' (xs.map (Model.Boundary.read (conV D.ctors k) (marker k) (idEnv k)))
        (ss.map (ival (idEnv k))) := by
    intro c' xs ss
    by_cases hc' : c' < c
    · simp only [hc', ↓reduceIte, conBefore, ↓reduceDIte]
      exact all_con_sound hW hD c' ps k (marker k) (idEnv k) (marker_kv k) xs ss
    · simp [hc', conBefore, Model.Boundary.read]
  have he := (Model.Boundary.read_eval (conV D.ctors k) (conBefore D.ctors c k) (marker k) (idEnv k) _ hH
    Tm.var (fun i => rs.reverse.getD i .zero) b).1
  rw [Model.Boundary.dims_env] at he
  exact he

theorem overlap_norm_near (hW : WfSig S) (hD : S[d]? = some (.data D)) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {ψ ψ' : I} {b b' : Tm} (hb : (ψ, b) ∈ C.bnd) (hb' : (ψ', b') ∈ C.bnd)
    (rs : List I) (hh : (ival (renv (rs.map (ival (idEnv k)))) (.and ψ ψ')).holds)
    (hn : NF D.ctors d (Ctor.paramVars D.params.length C.args.length) k
      (norm D.ctors d (Ctor.paramVars D.params.length C.args.length) c rs b))
    (hn' : NF D.ctors d (Ctor.paramVars D.params.length C.args.length) k
      (norm D.ctors d (Ctor.paramVars D.params.length C.args.length) c rs b')) :
    KubusCore.Boundary.Near
      (norm D.ctors d (Ctor.paramVars D.params.length C.args.length) c rs b)
      (norm D.ctors d (Ctor.paramVars D.params.length C.args.length) c rs b') := by
  apply hn.reflect hn'
  rw [denote_norm hW hD, denote_norm hW hD]
  exact agree_read hW hD (checks hW hD c C hC ψ b ψ' b' hb hb') (marker k) (marker_kv k) _ hh

end

end Model.Whnf.Boundary2
