import Model.Canon.KanData
import Model.Canon.ProjHcomp
import Model.Canon.KanFill

/-!
# Canonicity: composition in inductive types without path constructors (`hcompCon`)

A computable base is a constructor (its relation has no `hcomp` nodes), and so is the tube on its
face (`TubeCanon`), whose arguments are given uniformly by the projections (`hcompCon_premises`).
The composite is then the constructor of the componentwise composites (`hcompCon`): compositions
in the inductive type for recursive arguments (by induction on the relation of the base) and
heterogeneous compositions along the argument type lines for point arguments. The lines are
computable at valid earlier fillers, which needs the composition filler of the recursive
arguments, again by induction.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

/-- The computability clause of an inductive type's line for its argument types. -/
def ArgClause (S : Sig) {m : ℕ} (Θ : SData m) {n : ℕ} (f : Hom n m) (ps : Tm) : Prop :=
  ∀ k' (σ : ISub k' n) (c : ℕ) (C : Ctor) (args : List Tm), (dataD S Θ.idx).ctors[c]? = some C →
    args.length < C.args.length → C.isRec args.length = false →
    (∀ j (hj : j < args.length), C.isRec j = true →
      DR S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP S Θ f) k' σ.hom ((Tm.data Θ.idx ps).isub σ) args[j]) →
    (∀ j (hj : j < args.length), C.isRec j = false →
      dataP S Θ f k' σ.hom c j ((args.take j).map (semK S k'))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ (ps.isub σ).toList.reverse))
        args[j]) →
    (Comp S (tyLook (shapeV (Θ.restr (f.comp σ.hom))) c args.length (args.map (semK S k'))) k' k' (Hom.id k')).ty
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList (args.reverse ++ (ps.isub σ).toList.reverse))

/-- A recursive argument type, instantiated at parameters. -/
theorem argTy_rec_inst {C : Ctor} {j d np : ℕ} (hr : C.isRec j = true) {ps : Tm} (hps : IsList ps)
    (hpl : ps.toList.length = np) {L : List Tm} (hL : L.length = j) :
    (C.argTy d np j).substList (L ++ ps.toList.reverse) = .data d ps := by
  rw [argTy_rec hr, Tm.substList,
    show (Tm.data d (Ctor.paramVars np j)).subst _ I.var = Tm.data d ((Ctor.paramVars np j).substList _) from rfl,
    Meta.paramVars_substList hps hpl hL]

variable (hW : WfSig S)
include hW

/-- A constructor in the relation of an inductive type without path constructors, restricted and
retyped at a restriction of the type: its arguments are typed and computable there. -/
theorem con_restrict {Θ : SData m} (hΘ : Θ.Good)
    (ihT : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → KR S n (Θ.ty c j n g pre))
    {D : DataDecl} (hD : S[Θ.idx]? = some (.data D)) (hH : D.isHIT = false)
    {k0 : ℕ} {f : Hom k0 m} {P : Tm} (hall : ArgClause S Θ f P)
    {k' : ℕ} {g : Hom k' k0} {A t qs : Tm} {c : ℕ} {C : Ctor} {args : List Tm} {rs : List I}
    (hC : D.ctors[c]? = some C) (hrs : rs.length = C.dims) (hqs : qs = Tm.ofList qs.toList)
    (hAeq : TyEq S k' A (.data Θ.idx qs))
    (he : EqTm S k' .one [] t (.con Θ.idx c qs (Tm.ofList args) rs) A) (hlen : args.length = C.args.length)
    (hrec : ∀ j (hj : j < args.length), C.isRec j = true →
      DR S Θ.idx D (dataMem S Θ f) (dataP S Θ f) k' g (.data Θ.idx qs) args[j])
    (hpt : ∀ j (hj : j < args.length), C.isRec j = false →
      dataP S Θ f k' g c j ((args.take j).map (semK S k'))
        ((C.argTy Θ.idx D.params.length j).substList ((args.take j).reverse ++ qs.toList.reverse)) args[j])
    {k'' : ℕ} (σ' : ISub k'' k') (ρ : ISub k'' k0) (hg : g.comp σ'.hom = ρ.hom) {l : ℕ}
    (hpT : HasTy S k'' .one [] (.data Θ.idx (P.isub ρ)) (.univ l))
    (hA : TyEq S k'' (A.isub σ') (.data Θ.idx (P.isub ρ))) :
    HasTele0 S k'' .one [] (Tm.ofList (args.map (·.isub σ'))) (C.argTys Θ.idx D.params.length)
      (P.isub ρ).toList.reverse ∧
    EqTm S k'' .one [] (t.isub σ') (.con Θ.idx c (P.isub ρ) (Tm.ofList (args.map (·.isub σ'))) [])
      (.data Θ.idx (P.isub ρ)) ∧
    (∀ j (hj : j < args.length), C.isRec j = true →
      DR S Θ.idx D (dataMem S Θ f) (dataP S Θ f) k'' ρ.hom ((Tm.data Θ.idx P).isub ρ) ((args[j]).isub σ')) ∧
    (∀ j (hj : j < args.length), C.isRec j = false →
      RE S k'' ((C.argTy Θ.idx D.params.length j).substList
        (((args.map (·.isub σ')).take j).reverse ++ (P.isub ρ).toList.reverse)) ((args[j]).isub σ')) := by
  have hS := sigClosed_of_wfSig hW
  have hdD := dataD_eq hW hD
  have hrs0 : rs = [] := List.eq_nil_of_length_eq_zero (by rw [hrs, (nonHIT_ctor hH hC).1])
  subst hrs0
  set d := Θ.idx with hd
  set p := P.isub ρ with hp
  -- the restricted constructor
  have he' : EqTm S k'' .one [] (t.isub σ')
      (.con d c (qs.isub σ') (Tm.ofList (args.map (·.isub σ'))) []) (A.isub σ') := by
    have := EqTm.isubS hW he σ'
    rwa [show (Tm.con d c qs (Tm.ofList args) []).isub σ' =
      .con d c (qs.isub σ') ((Tm.ofList args).isub σ') [] from rfl, ofList_isub] at this
  have hqL : TyEq S k'' (.data d (qs.isub σ')) (.data d p) := (hAeq.isub hW σ').symm.trans hW hA
  have hcon := spec_to_minimal hW (HasTy.eqR he')
  obtain ⟨hI, -⟩ := gen_conF hcon rfl
  obtain ⟨-, D0, C0, hD0, hC0, hqs', hdq, hqt, haq, -, -⟩ := hI
  rw [hD] at hD0; cases hD0; rw [hC] at hC0; cases hC0
  obtain ⟨lq, eq⟩ := tyEq_eq hW hqL ⟨_, hpT⟩
  obtain ⟨D', hD', hPt⟩ := gen_data_tele (spec_to_minimal hW hpT) rfl
  rw [hD] at hD'; cases hD'
  have hPl : p = Tm.ofList p.toList := tele_isList hPt
  have hret := args_retype hW hD hC hqs' hPl hqt hPt (spec_to_minimal_eq hW eq) haq
  rw [toList_ofList] at hret
  obtain ⟨htele, hteq⟩ := hret
  have hMem : ∀ k1 (f1 : Hom k1 k0) t t' A, EqTm S k1 .one [] t t' A → dataMem S Θ f k1 f1 t →
      dataMem S Θ f k1 f1 t' := fun k1 f1 t t' A e hm => by unfold dataMem at hm ⊢; rwa [← semK_eq hW e]
  refine ⟨htele, ?_, ?_, ?_⟩
  · -- the constructor at the restricted parameters
    have hpd : HasTy0 S k'' .one [] (.data d p) (.univ D.level) := HasTy0.data hD (hW.2 d D hD).1 hPt
    have hcp := HasTy0.con (rs := []) hD hC hPl hpd hPt htele (by simp [(nonHIT_ctor hH hC).1]) (by simp)
    have hcq := HasTy0.conv hcp (EqTm0.symm (spec_to_minimal_eq hW eq))
    have eps := EqTele0.dataInj hD hqt hPt (spec_to_minimal_eq hW eq)
    have hc0 := HasTy0.con (rs := []) hD hC hqs' hdq hqt haq (by simp [(nonHIT_ctor hH hC).1]) (by simp)
    have ec := EqTm0.con hD hC hc0 hcq eps (EqTele0.refl haq) rfl (fun _ _ _ h => by simp at h)
    exact (he'.tyConv hA).trans (EqTm.tyConv (minimal_to_spec_eq ec) (.inr ⟨lq, eq⟩))
  · intro i hi hri
    have := DR.isub hW hΘ f ihT (hdD ▸ hrec i hi hri) k'' σ'
    rw [hdD, hg] at this
    exact DR.conv hW hMem this hqL (EqTm.refl ((this.typed).tyConv hqL))
  · intro i hi hri
    unfold ArgClause at hall
    rw [hdD] at hall
    set as := args.map (·.isub σ') with has
    have hasi : ∀ j (hj : j < args.length), as[j]'(by simp [as]; omega) = (args[j]).isub σ' := by
      intro j hj; simp [as]
    have hargT : ∀ j (hj : j < args.length), ∃ T, HasTy S k' .one [] args[j] T := by
      intro j hj
      cases hrj : C.isRec j
      · have := hpt j hj hrj; unfold dataP at this; exact ⟨_, (Comp_el_typed this).1⟩
      · exact ⟨_, (hrec j hj hrj).typed⟩
    have hpre : ∀ j, j ≤ args.length → ((args.take j).map (semK S k')).map (res σ'.hom) =
        (as.take j).map (semK S k'') := by
      intro j hj
      apply List.ext_getElem (by simp [as])
      intro x h1 h2
      simp only [List.getElem_map, List.getElem_take, as]
      obtain ⟨T, hT⟩ := hargT x (by simp at h1; omega)
      exact (semK_isubS hW hT σ').symm
    have hXq : ∀ j, j ≤ args.length → ((C.argTy d D.params.length j).substList
        ((args.take j).reverse ++ qs.toList.reverse)).isub σ' =
        (C.argTy d D.params.length j).substList ((as.take j).reverse ++ (qs.isub σ').toList.reverse) := by
      intro j hj
      rw [substList_isub (argTy_closed hS hD hC j), List.map_append, List.map_reverse, List.map_reverse,
        ← List.map_take, toList_isub hqs σ']
    let Valid : ℕ → Prop := fun j =>
      (∀ i (hi : i < j) (hi' : i < as.length), C.isRec i = true →
        DR S d D (dataMem S Θ f) (dataP S Θ f) k'' ρ.hom ((Tm.data d P).isub ρ) as[i]) ∧
      (∀ i (hi : i < j) (hi' : i < as.length), C.isRec i = false →
        dataP S Θ f k'' ρ.hom c i ((as.take i).map (semK S k''))
          ((C.argTy d D.params.length i).substList ((as.take i).reverse ++ p.toList.reverse)) as[i])
    have clause : ∀ j (hj : j < as.length), C.isRec j = false → Valid j →
        (Comp S (tyLook (shapeV (Θ.restr (f.comp ρ.hom))) c j ((as.take j).map (semK S k''))) k'' k''
          (Hom.id k'')).ty ((C.argTy d D.params.length j).substList ((as.take j).reverse ++ p.toList.reverse)) := by
      intro j hj hr hv
      have hlj : (as.take j).length = j := by simp; omega
      have := hall k'' ρ c C (as.take j) hC (by simp [as] at hj ⊢; omega) (by rw [hlj]; exact hr)
        (fun i hi hri => by
          rw [hlj] at hi; rw [List.getElem_take]; exact hv.1 i hi (by omega) hri)
        (fun i hi hri => by
          rw [hlj] at hi; rw [List.getElem_take, List.take_take, Nat.min_eq_left hi.le]
          exact hv.2 i hi (by omega) hri)
      rwa [hlj] at this
    have hrecR : ∀ i (hi : i < args.length), C.isRec i = true →
        DR S d D (dataMem S Θ f) (dataP S Θ f) k'' ρ.hom ((Tm.data d P).isub ρ) (as[i]'(by simp [as]; omega)) := by
      intro i hi hri
      have := DR.isub hW hΘ f ihT (hdD ▸ hrec i hi hri) k'' σ'
      rw [hdD, hg, ← hasi i hi] at this
      exact DR.conv hW hMem this hqL (EqTm.refl ((this.typed).tyConv hqL))
    have hptR : ∀ i (hi : i < args.length), C.isRec i = false →
        dataP S Θ f k'' ρ.hom c i ((as.take i).map (semK S k''))
          ((C.argTy d D.params.length i).substList ((as.take i).reverse ++ (qs.isub σ').toList.reverse))
          (as[i]'(by simp [as]; omega)) := by
      intro i hi hri
      have := dataP_isub hΘ f ihT (hpt i hi hri) σ'
      rw [hg, hpre i hi.le, hXq i hi.le, ← hasi i hi] at this
      exact this
    have conv : ∀ j (hj : j < args.length), C.isRec j = false → Valid j →
        RE S k'' ((C.argTy d D.params.length j).substList ((as.take j).reverse ++ p.toList.reverse))
          (as[j]'(by simp [as]; omega)) := by
      intro j hj hr hv
      have tyXp := clause j (by simp [as]; omega) hr hv
      obtain ⟨l', e⟩ := hteq j (by simp [as]; omega)
      have eT : TyEq S k'' ((C.argTy d D.params.length j).substList ((as.take j).reverse ++ (qs.isub σ').toList.reverse))
          ((C.argTy d D.params.length j).substList ((as.take j).reverse ++ p.toList.reverse)) :=
        .inr ⟨l', minimal_to_spec_eq e⟩
      have hel := hptR j hj hr
      unfold dataP at hel
      have hre : RE S k'' ((C.argTy d D.params.length j).substList ((as.take j).reverse ++ (qs.isub σ').toList.reverse))
          (as[j]'(by simp [as]; omega)) := by
        unfold RE; rw [semK_tyEq hW eT, ← Comp_eq_semK tyXp]; exact hel
      exact hre.conv_ty hW eT
    have key : ∀ j, j ≤ args.length → Valid j := by
      intro j
      induction j with
      | zero => intro _; exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      | succ j ih =>
        intro hj
        have hv := ih (by omega)
        refine ⟨fun i hi hi' hri => ?_, fun i hi hi' hri => ?_⟩
        · by_cases hij : i < j
          · exact hv.1 i hij hi' hri
          obtain rfl : i = j := by omega
          exact hrecR i (by omega) hri
        · by_cases hij : i < j
          · exact hv.2 i hij hi' hri
          obtain rfl : i = j := by omega
          have tyXp := clause i hi' hri hv
          show (Comp S _ k'' k'' (Hom.id k'')).el _ _
          rw [Comp_eq_semK tyXp]
          exact conv i (by omega) hri hv
    rw [← hasi i hi]
    exact conv i hi hri ⟨fun i' hi'' hi' hr' => (key args.length (Nat.le_refl _)).1 i' (by omega) hi' hr',
      fun i' hi'' hi' hr' => (key args.length (Nat.le_refl _)).2 i' (by omega) hi' hr'⟩

/-- An element in the relation of an inductive type without path constructors is a constructor,
at any restriction and retyping. -/
theorem dr_canon {Θ : SData m} (hΘ : Θ.Good)
    (ihT : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → KR S n (Θ.ty c j n g pre))
    {D : DataDecl} (hD : S[Θ.idx]? = some (.data D)) (hH : D.isHIT = false)
    {k0 : ℕ} {f : Hom k0 m} {P : Tm} (hall : ArgClause S Θ f P)
    {k' : ℕ} {g : Hom k' k0} {A t : Tm} (hdr : DR S Θ.idx D (dataMem S Θ f) (dataP S Θ f) k' g A t)
    {k'' : ℕ} (σ' : ISub k'' k') (ρ : ISub k'' k0) (hg : g.comp σ'.hom = ρ.hom) {l : ℕ}
    (hpT : HasTy S k'' .one [] (.data Θ.idx (P.isub ρ)) (.univ l))
    (hA : TyEq S k'' (A.isub σ') (.data Θ.idx (P.isub ρ))) :
    ∃ c C X, D.ctors[c]? = some C ∧ X.length = C.args.length ∧
      HasTele0 S k'' .one [] (Tm.ofList X) (C.argTys Θ.idx D.params.length) (P.isub ρ).toList.reverse ∧
      EqTm S k'' .one [] (t.isub σ') (.con Θ.idx c (P.isub ρ) (Tm.ofList X) []) (.data Θ.idx (P.isub ρ)) ∧
      (∀ j (hj : j < X.length), C.isRec j = true →
        DR S Θ.idx D (dataMem S Θ f) (dataP S Θ f) k'' ρ.hom ((Tm.data Θ.idx P).isub ρ) X[j]) ∧
      (∀ j (hj : j < X.length), C.isRec j = false →
        RE S k'' ((C.argTy Θ.idx D.params.length j).substList ((X.take j).reverse ++ (P.isub ρ).toList.reverse)) X[j]) := by
  cases hdr with
  | con hm hC hrs hsc hqs hAeq he hlen hrec hpt =>
    obtain ⟨h1, h2, h3, h4⟩ := con_restrict hW hΘ ihT hD hH hall hC hrs hqs hAeq he hlen hrec hpt σ' ρ hg hpT hA
    refine ⟨_, _, _, hC, by simpa using hlen, h1, h2, fun j hj hr => ?_, fun j hj hr => ?_⟩
    · have := h3 j (by simpa using hj) hr; simpa using this
    · have := h4 j (by simpa using hj) hr; simpa using this
  | hcomp _ hH' => rw [hH] at hH'; cases hH'

/-- A computable tube in an inductive type without path constructors is a constructor at its
faces, with computable arguments. -/
theorem tube_canon {Θ : SData m} (hΘ : Θ.Good)
    (ihT : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → KR S n (Θ.ty c j n g pre))
    (hKR : KR S m (dataC Θ)) {D : DataDecl} (hD : S[Θ.idx]? = some (.data D)) (hH : D.isHIT = false)
    {k0 : ℕ} {f : Hom k0 m} {P : Tm} (hT : (Comp S (dataC Θ) m k0 f).ty (.data Θ.idx P))
    (hall : ArgClause S Θ f P) {K : ℕ} (ρ : ISub K k0) {l : ℕ}
    (hpT : HasTy S K .one [] (.data Θ.idx (P.isub ρ)) (.univ l)) {φ : I} {u : Tm}
    (hu : TubeC S K (.data Θ.idx (P.isub ρ)) φ u) {k1 : ℕ} (σ : ISub k1 K) {r : I} (hr : r.Scoped k1)
    (hh : (ival (idEnv k1) (φ.subst σ.τ)).holds) :
    ∃ c C X, D.ctors[c]? = some C ∧ X.length = C.args.length ∧
      HasTele0 S k1 .one [] (Tm.ofList X) (C.argTys Θ.idx D.params.length) ((P.isub ρ).isub σ).toList.reverse ∧
      EqTm S k1 .one [] ((u.isub σ.up).dinst r) (.con Θ.idx c ((P.isub ρ).isub σ) (Tm.ofList X) [])
        (.data Θ.idx ((P.isub ρ).isub σ)) ∧
      (∀ j (hj : j < X.length), C.isRec j = true → RE S k1 (.data Θ.idx ((P.isub ρ).isub σ)) X[j]) ∧
      (∀ j (hj : j < X.length), C.isRec j = false →
        RE S k1 ((C.argTy Θ.idx D.params.length j).substList ((X.take j).reverse ++ ((P.isub ρ).isub σ).toList.reverse))
          X[j]) := by
  have hdD := dataD_eq hW hD
  have hw := hu k1 σ r hr hh
  have hTy := (hKR k0 f k1 (ρ.comp σ) (.data Θ.idx P) (.data Θ.idx P)).1 hT
  have e1 : (Tm.data Θ.idx (P.isub ρ)).isub σ = (Tm.data Θ.idx P).isub (ρ.comp σ) := Tm.isub_isub (Tm.data Θ.idx P) ρ σ
  rw [e1] at hw
  have hdr := DR_of_RE hW hTy hw
  rw [hdD] at hdr
  have hpT' := HasTy.isubS hW hpT σ
  rw [e1] at hpT'
  have hwc : ((u.isub σ.up).dinst r).closedB 0 k1 = true := closed_of_ty hW (Comp_el_typed hw).1
  have hAc : ((Tm.data Θ.idx P).isub (ρ.comp σ)).closedB 0 k1 = true := closed_of_ty hW hpT'
  obtain ⟨c, C, X, hC, hl, h1, h2, h3, h4⟩ := dr_canon hW hΘ ihT hD hH hall hdr (ISub.id k1) (ρ.comp σ)
    (by rw [ISub.hom_id, Hom.comp_id]) hpT' (by rw [isub_id_of_closed hAc]; exact .inl rfl)
  rw [isub_id_of_closed hwc] at h2
  have e2 : (P.isub ρ).isub σ = P.isub (ρ.comp σ) := Tm.isub_isub _ _ _
  rw [e2]
  refine ⟨c, C, X, hC, hl, h1, h2, fun j hj hr => ?_, h4⟩
  have := h3 j hj hr
  rw [← hdD] at this
  exact RE_of_DR hW hTy this

/-- The projections of a computable tube are computable at its faces. -/
theorem tube_proj {Θ : SData m} (hΘ : Θ.Good)
    (ihT : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → KR S n (Θ.ty c j n g pre))
    (hKR : KR S m (dataC Θ)) {D : DataDecl} (hD : S[Θ.idx]? = some (.data D)) (hH : D.isHIT = false)
    {k0 : ℕ} {f : Hom k0 m} {P : Tm} (hT : (Comp S (dataC Θ) m k0 f).ty (.data Θ.idx P))
    (hall : ArgClause S Θ f P) {K : ℕ} (ρ : ISub K k0)
    (hpT : HasTy S K .one [] (.data Θ.idx (P.isub ρ)) (.univ D.level)) {φ : I} {u : Tm} (hφs : φ.Scoped K)
    (hut : u.closedB 0 (K + 1) = true) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {X : List Tm}
    (hside : EqTm S K (cof .one φ) [] (u.dinst .zero) (.con Θ.idx c (P.isub ρ) (Tm.ofList X) [])
      (.data Θ.idx (P.isub ρ)))
    (hu : TubeC S K (.data Θ.idx (P.isub ρ)) φ u) {k1 : ℕ} (σ : ISub k1 K) {r : I} (hr : r.Scoped k1)
    (hh : (ival (idEnv k1) (φ.subst σ.τ)).holds) {j : ℕ} (hj : j < C.args.length) :
    RE S k1 ((C.argTy Θ.idx D.params.length j).substList
      ((((List.range C.args.length).map fun i => proj Θ.idx D ((P.isub ρ).isub σ) c C i ((u.isub σ.up).dinst r)).take j).reverse ++
        ((P.isub ρ).isub σ).toList.reverse))
      (proj Θ.idx D ((P.isub ρ).isub σ) c C j ((u.isub σ.up).dinst r)) := by
  have hS := sigClosed_of_wfSig hW
  have hcan : TubeCanon S K Θ.idx D (P.isub ρ) φ u := fun k2 σ2 r2 hr2 hh2 => by
    obtain ⟨c', C', X', hC', -, h1, h2, -⟩ := tube_canon hW hΘ ihT hKR hD hH hT hall ρ hpT hu σ2 hr2 hh2
    exact ⟨c', C', X', hC', h1, h2⟩
  obtain ⟨c', C', X', hC', hl, hX', he, hrec, hpt⟩ := tube_canon hW hΘ ihT hKR hD hH hT hall ρ hpT hu σ hr hh
  obtain rfl := (tube_tag hW hD hH hC hpT hφs hut hside hcan σ hr hh hC' he).symm
  rw [hC] at hC'; injection hC' with hCC; subst hCC
  set q := (P.isub ρ).isub σ with hq
  set w := (u.isub σ.up).dinst r with hw
  have hqT := HasTy.isubS hW hpT σ
  have H := PD.of hW hD hH (spec_to_minimal hW hqT)
  set Y := (List.range C.args.length).map fun i => proj Θ.idx D q c C i w with hY
  have hYl : Y.length = X'.length := by simp [Y, hl]
  have hYX : ∀ i (h1 : i < X'.length) (h2 : i < Y.length), EqTm0 S k1 .one [] Y[i] X'[i]
      ((C.argTy Θ.idx D.params.length i).substList ((X'.take i).reverse ++ q.toList.reverse)) := by
    intro i h1 h2
    have := proj_canon hS hW H hC hX' (spec_to_minimal_eq hW he) (i := i) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
    simpa [Y] using this
  have tc := tele_conv hW hD hC H.hpsL H.hpt H.hdata hX' hYl hYX
  have eT := tc.2.2 j (by simp [Y]; exact hj)
  have hYj : Y[j]'(by simp [Y]; exact hj) = proj Θ.idx D q c C j w := by simp [Y]
  have hXj : RE S k1 ((C.argTy Θ.idx D.params.length j).substList ((X'.take j).reverse ++ q.toList.reverse))
      (X'[j]'(by omega)) := by
    cases hrj : C.isRec j
    · exact hpt j (by omega) hrj
    · rw [argTy_rec_inst (ps := q) hrj H.hpsL H.hpl (by simp; omega)]
      exact hrec j (by omega) hrj
  rw [← hYj]
  exact hXj.conv hW (.inr ⟨_, minimal_to_spec_eq (EqTm0.symm eT)⟩)
    (EqTm.symm (EqTm.tyConv (minimal_to_spec_eq (hYX j (by omega) (by simp [Y]; exact hj)))
      (.inr ⟨_, minimal_to_spec_eq (EqTm0.symm eT)⟩)))

/-- The type line of a point argument along `hcompCon`: typed, at its start the type of the
argument, at its end the type of the composite, and on the face the type of the tube's argument. -/
theorem hcompCon_pt_types {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} (hD : S[d]? = some (.data D))
    (hH : D.isHIT = false) (hC : D.ctors[c]? = some C) {K : ℕ} {p : Tm} {φ : I} {us as : List Tm}
    (hdT : HasTy0 S K .one [] (.data d p) (.univ D.level)) (hφ : φ.Scoped K)
    (h6 : HasTele0 S K .one [] (Tm.ofList as) (C.argTys d D.params.length) p.toList.reverse)
    (h7 : HasTele0 S (K + 1) (cof .one φ).shift [] (Tm.ofList us) (C.argTys d D.params.length)
      p.dshift.toList.reverse)
    (h9 : EqTele0 S K (cof .one φ) [] ((Tm.ofList us).dinst .zero) (Tm.ofList as) (C.argTys d D.params.length)
      p.toList.reverse)
    {j : ℕ} {A0 : Tm} (hA0 : C.args[j]? = some (.point A0)) :
    let Ac := C.argTy d D.params.length
    let L := Meta.hLine C Ac (.data d p) p.dshift.toList φ us as j
    let osAll := (List.range C.args.length).map (Meta.hOut C Ac (.data d p) p.dshift.toList φ us as)
    HasTy0 S (K + 1) .one [] L (.univ D.level) ∧
    EqTm S K .one [] (L.dinst .zero) (A0.substList ((as.take j).reverse ++ p.toList.reverse)) (.univ D.level) ∧
    EqTm S K .one [] (L.dinst .one) (A0.substList ((osAll.take j).reverse ++ p.toList.reverse)) (.univ D.level) ∧
    EqTm0 S (K + 1) (cof .one φ).shift [] L (A0.substList ((us.take j).reverse ++ p.dshift.toList.reverse))
      (.univ D.level) := by
  intro Ac L osAll
  have hS := sigClosed_of_wfSig hW
  have hjC : j < C.args.length := (List.getElem?_eq_some_iff.1 hA0).1
  have H := PD.of hW hD hH hdT
  have hΦs : ((cof .one φ).shift).Scoped (K + 1) := I.scoped_shift ⟨trivial, hφ⟩
  have hd1 : HasTy0 S (K + 1) (cof .one φ).shift [] (.data d p.dshift) (.univ D.level) :=
    HasTy0.restrict hΦs (ent_one _) (HasTy0.dwk hS (Φ := .one) (Γ := []) hdT)
  have H1 := PD.of hW hD hH hd1
  have hpl := H.hpl
  have hpl1 := H1.hpl
  have hal : as.length = C.args.length := by
    have := tele_length h6; rwa [toList_ofList, argTys_length] at this
  have hul : us.length = C.args.length := by
    have := tele_length h7; rwa [toList_ofList, argTys_length] at this
  obtain ⟨T1, TO, E0, E1, Eφ, -⟩ := hcompCon_inv hS hW (htr_of hW d) hD hC (H.hpsL) (args := Tm.ofList as)
    (by rw [toList_ofList]) (uargs := Tm.ofList us) (by rw [toList_ofList]) h6 h7 h9 hdT hφ j hjC.le
  simp only [toList_ofList] at T1 TO E0 E1 Eφ
  have hw : Wf0 S K .one [] := Wf0.nil trivial
  have hf : ∀ (r : I), r.Scoped K → ∀ t B, HasTy0 S (K + 1) I.one.shift (Ctx.dshift []) t B →
      HasTy0 S K .one [] (t.subst Tm.var (I.inst0 r)) (B.subst Tm.var (I.inst0 r)) :=
    fun r hr t B h => HasTy0.dsubst hS h hr
  have hP := pt_typed hW (htr_of hW d) hD hC hA0
  have hpost : ∀ (σ : Nat → Tm) (τ' : Nat → I),
      (A0.ren (C.pointRen j) id).subst (fun x => (σ x).subst Tm.var τ') (fun i => (I.var i).subst τ') =
        ((A0.ren (C.pointRen j) id).subst σ I.var).subst Tm.var τ' :=
    fun σ τ' => (subst_subst _ _ _ _ _).symm
  have hAk : Ac j = A0 := by simp [Ac, Ctor.argTy, hA0]
  set Fall := Meta.hFills C Ac (.data d p) p.dshift.toList φ us as C.args.length with hFall
  have hFt : Fall.take j = Meta.hFills C Ac (.data d p) p.dshift.toList φ us as j := by
    have := Meta.hFills_take C Ac (.data d p) p.dshift.toList φ us as j (C.args.length - j)
    rwa [show j + (C.args.length - j) = C.args.length by omega] at this
  have hFl : Fall.length = C.args.length := Meta.hFills_length _ _ _ _ _ _ _ _
  have hLeq : (A0.ren (C.pointRen j) id).subst (lsub (ptL C Fall p.dshift.toList.reverse j) 0) I.var = L := by
    rw [pt_inst hW hD hC hA0 (by omega) (by simp [hpl1]) 0 I.var, hFt]
    show _ = (Ac j).substList _
    rw [hAk]
  have h0 : ∀ (Ψ : ℕ) (Φ : I), Wf0 S Ψ Φ [] → ∀ (τ σ : Nat → _), TySub S 0 .one [] Ψ Φ [] σ τ :=
    fun Ψ Φ hw τ σ => tySub_nil (fun i hi => absurd hi (Nat.not_lt_zero _)) (ent_one _) hw
  have hPP0 := tySub_params hS hD H.hpt 0 (h0 K .one hw I.var) _ (Nat.le_refl _)
  rw [List.take_of_length_le (by omega)] at hPP0
  have TA := tySub_points hS hW hD hC hPP0 (by simpa using h6) hpl j hjC.le
  simp only [toList_ofList] at TA
  have hPP1 := tySub_params hS hD H1.hpt 0 (h0 (K + 1) _ H1.hw I.var) _ (Nat.le_refl _)
  rw [List.take_of_length_le (by omega)] at hPP1
  have TU := tySub_points hS hW hD hC hPP1 (by simpa using h7) hpl1 j hjC.le
  simp only [toList_ofList] at TU
  have T10 := T1.post (I.inst0 .zero) hw (hf .zero trivial)
  have T11 := T1.post (I.inst0 .one) hw (hf .one trivial)
  have e0 := (sub_ty hS hP).2.2 T10 TA E0
  rw [hpost, hLeq, pt_inst hW hD hC hA0 (by omega) (by simp [hpl]) 0 I.var] at e0
  have e1 := (sub_ty hS hP).2.2 T11 TO E1
  rw [hpost, hLeq, pt_inst hW hD hC hA0 (by simp [osAll]; omega) (by simp [hpl]) 0 I.var] at e1
  have eφ := (sub_ty hS hP).2.2 (T1.restrict hΦs (ent_shift (ent_one _))) TU Eφ
  rw [hLeq, pt_inst hW hD hC hA0 (by omega) (by simp [hpl1]) 0 I.var] at eφ
  have hL := (sub_ty hS hP).2.1 T1
  rw [hLeq] at hL
  exact ⟨hL, minimal_to_spec_eq e0, minimal_to_spec_eq e1, eφ⟩

/-- The projections of a tube commute with its restrictions at a point. -/
theorem proj_tube_isub {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} (hD : S[d]? = some (.data D))
    (hC : D.ctors[c]? = some C) {j : ℕ} (hj : j < C.args.length) {K k1 : ℕ} {ps u : Tm}
    (hps1 : IsList ps.dshift) (hpl1 : ps.dshift.toList.length = D.params.length) (σ : ISub k1 K) {r : I}
    (hr : r.Scoped k1) :
    (proj d D ps.dshift c C j u).isub (ISub.cons r hr σ) = proj d D (ps.isub σ) c C j ((u.isub σ.up).dinst r) := by
  have hS := sigClosed_of_wfSig hW
  show (proj d D ps.dshift c C j u).subst Tm.var (ISub.cons r hr σ).τ = _
  rw [proj_dsubst hS hD hC hj hps1 hpl1, ← isub_eq_subst, ← isub_eq_subst, dshift_isub_cons, isub_up_dinst _ σ r hr]

/-- Composition of a constructor in an inductive type without path constructors, given the
composition of its recursive arguments at all restrictions. -/
theorem hcompCon_RE {Θ : SData m} (hΘ : Θ.Good)
    (ihT : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → KR S n (Θ.ty c j n g pre))
    (hcodeK : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre →
      (∀ k3 (h3 : Hom k3 n) (A : Tm), (Comp S (Θ.ty c j n g pre) n k3 h3).ty A → KanH S k3 A) ∧
      (∀ k3 (h3 : Hom (k3 + 1) n) (A : Tm), (Comp S (Θ.ty c j n g pre) n (k3 + 1) h3).ty A → KanT S k3 A))
    (hKR : KR S m (dataC Θ)) {D : DataDecl} (hD : S[Θ.idx]? = some (.data D)) (hH : D.isHIT = false)
    {k0 : ℕ} {f : Hom k0 m} {P : Tm} (hT : (Comp S (dataC Θ) m k0 f).ty (.data Θ.idx P))
    (hall : ArgClause S Θ f P) {K : ℕ} (ρ : ISub K k0)
    (hpT : HasTy S K .one [] (.data Θ.idx (P.isub ρ)) (.univ D.level)) {φ : I} {u : Tm}
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {X : List Tm}
    (hX : HasTele0 S K .one [] (Tm.ofList X) (C.argTys Θ.idx D.params.length) (P.isub ρ).toList.reverse)
    (hty : HasTy S K .one [] (.hcomp (.data Θ.idx (P.isub ρ)) φ u (.con Θ.idx c (P.isub ρ) (Tm.ofList X) []))
      (.data Θ.idx (P.isub ρ)))
    (hu : TubeC S K (.data Θ.idx (P.isub ρ)) φ u)
    (hrecH : ∀ i (hi : i < X.length), C.isRec i = true → ∀ K' (σ : ISub K' K) (φ' : I) (u' : Tm),
      HasTy S K' .one [] (.hcomp (.data Θ.idx (P.isub (ρ.comp σ))) φ' u' (X[i].isub σ))
        (.data Θ.idx (P.isub (ρ.comp σ))) →
      TubeC S K' (.data Θ.idx (P.isub (ρ.comp σ))) φ' u' →
      RE S K' (.data Θ.idx (P.isub (ρ.comp σ))) (.hcomp (.data Θ.idx (P.isub (ρ.comp σ))) φ' u' (X[i].isub σ)))
    (hrecR : ∀ i (hi : i < X.length), C.isRec i = true →
      DR S Θ.idx D (dataMem S Θ f) (dataP S Θ f) K ρ.hom ((Tm.data Θ.idx P).isub ρ) X[i])
    (hptR : ∀ i (hi : i < X.length), C.isRec i = false →
      RE S K ((C.argTy Θ.idx D.params.length i).substList ((X.take i).reverse ++ (P.isub ρ).toList.reverse)) X[i]) :
    RE S K (.data Θ.idx (P.isub ρ)) (.hcomp (.data Θ.idx (P.isub ρ)) φ u (.con Θ.idx c (P.isub ρ) (Tm.ofList X) [])) := by
  have hS := sigClosed_of_wfSig hW
  have hdD := dataD_eq hW hD
  obtain ⟨l0, ⟨-, hφs, hut, -, hside0⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) (spec_to_minimal hW hty) rfl
  have hside : EqTm S K (cof .one φ) [] (u.dinst .zero) (.con Θ.idx c (P.isub ρ) (Tm.ofList X) [])
      (.data Θ.idx (P.isub ρ)) := minimal_to_spec_eq hside0
  have hutc : u.closedB 0 (K + 1) = true := closed_ty hut
  have hcan : TubeCanon S K Θ.idx D (P.isub ρ) φ u := fun k2 σ2 r2 hr2 hh2 => by
    obtain ⟨c', C', X', hC', -, h1, h2, -⟩ := tube_canon hW hΘ ihT hKR hD hH hT hall ρ hpT hu σ2 hr2 hh2
    exact ⟨c', C', X', hC', h1, h2⟩
  obtain ⟨G1, G2, G3, G4⟩ := hcompCon_premises hW hD hH hC hpT hφs hut hside hX hcan
  set d := Θ.idx with hd
  set p := P.isub ρ with hp
  set Ac := C.argTy d D.params.length with hAc
  set us := (List.range C.args.length).map fun j => proj d D p.dshift c C j u with hus
  have H := PD.of hW hD hH (spec_to_minimal hW hpT)
  have hΦs : ((cof .one φ).shift).Scoped (K + 1) := I.scoped_shift ⟨trivial, hφs⟩
  have H1 := PD.of hW hD hH (HasTy0.restrict hΦs (ent_one _) (HasTy0.dwk hS (Φ := .one) (Γ := [])
    (spec_to_minimal hW hpT)))
  have hXl : X.length = C.args.length := by
    have := tele_length hX; rwa [toList_ofList, argTys_length] at this
  have hul : us.length = C.args.length := by simp [us]
  -- the contractum
  have e_hc := EqTm0.hcompCon (qs := p) hD hH hC H.hpsL (args := Tm.ofList X) (by rw [toList_ofList])
    (uargs := Tm.ofList us) (by rw [toList_ofList]) hX G1 G2 G3 (spec_to_minimal hW hty)
  simp only [toList_ofList] at e_hc
  have heq := Meta.hcompTele_eq C Ac (.data d p) p.dshift.toList φ us X us X 0 rfl rfl (by rw [hul, hXl])
  simp only [hXl, ← List.range_eq_range'] at heq
  rw [show ([] : List Tm) = (Meta.hFills C Ac (.data d p) p.dshift.toList φ us X 0).reverse from rfl, heq] at e_hc
  set outs := (List.range C.args.length).map (Meta.hOut C Ac (.data d p) p.dshift.toList φ us X) with houts
  obtain ⟨-, -, -, -, -, Tel⟩ := hcompCon_inv hS hW (htr_of hW d) hD hC H.hpsL (args := Tm.ofList X)
    (by rw [toList_ofList]) (uargs := Tm.ofList us) (by rw [toList_ofList]) hX G1 G3 (spec_to_minimal hW hpT) hφs
    C.args.length (Nat.le_refl _)
  simp only [toList_ofList] at Tel
  have hol : outs.length = C.args.length := by simp [outs]
  refine (RE_con hW hD hpT H.hpsL hC hol (rs := []) (by simp [(nonHIT_ctor hH hC).1]) (by simp)
    (HasTy.eqR (minimal_to_spec_eq e_hc)) (fun j hj hr => ?_) (fun j hj hr => ?_)).conv hW (TyEq.refl _)
    (EqTm.symm (minimal_to_spec_eq e_hc))
  · have hjC : j < C.args.length := by omega
    have hog : outs[j] = .hcomp (.data d p) φ (us.getD j .abort) (X.getD j .abort) := by
      simp [outs, Meta.hOut, hr]
    have hXj : X.getD j .abort = X[j]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hXc : (X[j]'(by omega)).closedB 0 K = true := by
      have := tele_get hX j _ _ (by rw [toList_ofList]; exact List.getElem?_eq_getElem (by omega))
        (argTys_get hjC)
      exact closed_ty this
    have htyj : HasTy S K .one [] outs[j] (.data d p) := by
      have := Tel j hjC
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
        argTy_rec_inst (ps := p) hr H.hpsL H.hpl (by simp; omega)] at this
      exact minimal_to_spec this
    rw [hog] at htyj ⊢
    have := hrecH j (by omega) hr K (ISub.id K) φ (us.getD j .abort)
    rw [ISub.comp_id, isub_id_of_closed hXc, ← hXj] at this
    refine this htyj fun k1 σ r hr1 hh => ?_
    rw [isub_up_dinst _ σ r hr1]
    have hug : us.getD j .abort = proj d D p.dshift c C j u := by
      simp [us, List.getD_eq_getElem?_getD, hjC]
    rw [hug, proj_tube_isub hW hD hC hjC H1.hpsL H1.hpl σ hr1]
    have := tube_proj hW hΘ ihT hKR hD hH hT hall ρ hpT hφs hutc hC hside hu σ hr1 hh hjC
    have Hσ : PD S k1 .one d D (p.isub σ) := PD.of hW hD hH (spec_to_minimal hW (HasTy.isubS hW hpT σ))
    rwa [argTy_rec_inst (ps := p.isub σ) hr Hσ.hpsL Hσ.hpl (by simp; omega)] at this
  · sorry

end

end Model.Canon
