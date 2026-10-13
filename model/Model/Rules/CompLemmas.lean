import Model.Rules.KanLemmas

/-!
# The Kan computation rules

For each computation rule `op (F …) … ≡ contractum`, the code's operation is the semantic reading
of the contractum; here we compute the denotation of the contractum at a point where the redex
is defined and show that it agrees.
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

theorem TubeOK.congr {c : V} {f : Hom k m} {φ : Cof k} {u u' : Tube k} {u0 : V} (hφ : φ.IsCof)
    (h : ∀ n (g : Hom n k) r, (φ.restr g).holds → u n g r = u' n g r) (hu : TubeOK c f φ u u0) :
    TubeOK c f φ u' u0 where
  mem n g r hg := h n g r hg ▸ hu.mem n g r hg
  coh n g r hg n' g' := by
    have hg' : (φ.restr (g.comp g')).holds := by
      rw [← Cof.restr_restr]; exact Cof.IsCof.holds_restr (hφ.restr g) hg g'
    rw [← h n g r hg, ← h n' _ _ hg']; exact hu.coh n g r hg n' g'
  base n g hg := by rw [← h n g _ hg]; exact hu.base n g hg

theorem sem_app_shift_var0 (t : Tm) (ρ : IEnv m) (γ : ℕ → V) (a : V) :
    sem S (.app t.shift (.var 0)) m ρ (TEnv.cons γ a) = appV m (sem S t m ρ γ) a := by
  rw [sem_app_of_nat (natural_var S 0 _ _), sem_shift, sem_var, TEnv.cons_zero]

theorem below_piC_famAt (A B : V) (hB : IsKV m B) (g : Hom n m) (a : V)
    (ha : ∃ y, ZFSet.pair a y ∈ dat B n g) : Below (apZ (dat B n g) a) (piC m A B) := by
  have h1 : Below (apZ (dat B n g) a) B := (below_apZ ha).trans (below_dat hB _)
  have h2 : Below (res (Hom.id m) B) (piC m A B) := by
    unfold piC
    refine Below.trans ?_ (below_dat_mkKV _ (Hom.id m))
    simp only [piDatum, quad, tagZ]
    exact ((below_pair_right _ _).trans (below_pair_right _ _)).trans (below_pair_left _ _)
  rw [res_id hB] at h2
  exact h1.trans h2

/-- The Π data of a good Π-code at a point. -/
theorem TyOK.pi_data {A B : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : TyOK S (.pi A B) m ρ γ) :
    let Av := sem S A m ρ γ
    let Bf := famV m Av fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)
    IsKV m Av ∧ sem S (.pi A B) m ρ γ = piC m Av Bf ∧ Fib Av m ∧ FamOK Av Bf m ∧
      ∃ l ≤ maxLevel, ∀ n (g : Hom n m), ∀ a ∈ El Av g,
        apZ (dat Bf n g) a ∈ Vt l ∧ WF l n (apZ (dat Bf n g) a) := by
  intro Av Bf
  obtain ⟨hAkv, l, hl, hV, hWF⟩ := h.pi_at
  rw [sem_pi hAkv] at hV hWF
  obtain ⟨hAWF, hfam, hcoh⟩ := WF.pi_inv hAkv (isKV_famV _ _) hWF
  refine ⟨hAkv, sem_pi hAkv, hAWF.fib, ⟨isKV_famV _ _, fun k f => ?_, fun k f a ha => (hfam k f a ha).fib,
    hcoh⟩, l, hl, fun n g a ha => ⟨?_, hfam n g a ha⟩⟩
  · rw [dat_famV]
    exact fnZ_congr fun a ha => (apZ_fnZ (fun a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) ha).symm
  · exact Vt_below (below_piC_famAt _ _ (isKV_famV _ _) _ _ ⟨_, by rw [dat_famV]; exact mem_fnZ.2 ⟨_, ha, rfl⟩⟩) hV

/-! ### hcompPi -/

theorem sem_hcompPi {A B u u0 : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V}
    (hc : HcompCond S (.pi A B) φ u u0 m ρ γ) :
    sem S (Tm.hcompPi A B φ u u0) m ρ γ = sem S (.hcomp (.pi A B) φ u u0) m ρ γ := by
  obtain ⟨hAkv, hsem, hAfib, hfam, l, hl, hfamW⟩ := (show TyOK S (.pi A B) m ρ γ from hc.1).pi_data
  have hu0 := hc.2.2.1
  have hu := hc.2.1
  have hu0nat := hc.2.2.2.2
  rw [hsem] at hu0 hu
  rw [sem_hcomp hc, hsem, hcompAt_piC hAfib hfam hu0 hu]
  simp only [Tm.hcompPi]
  rw [sem_lam]
  unfold hcompPiF lamV
  congr 1; funext n g
  dsimp only
  rw [El_res, Hom.id_comp]
  apply fnZ_congr; intro v hv
  simp only [dat_res, Hom.id_comp]
  have hv' : v ∈ El (res (Hom.id m) (sem S A m ρ γ)) g := by rw [El_res, Hom.id_comp]; exact hv
  obtain ⟨hC, hb, hut⟩ := hcompPi_inner hAfib hfam (isCof_ival_face ρ φ) hu0 hu g hv'
  simp only [dat_res, Hom.id_comp] at hC hb hut
  set Bf := famV m (sem S A m ρ γ) fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)
  have eB : sem S B n (ρ.restr g) (TEnv.cons (TEnv.restr γ g) v) = apZ (dat Bf n g) v :=
    (apZ_dat_famV (sem S A m ρ γ) (fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) g hv).symm
  have eb : sem S (.app u0.shift (.var 0)) n (ρ.restr g) (TEnv.cons (TEnv.restr γ g) v) =
      appV n (res g (sem S u0 m ρ γ)) v := by
    rw [sem_app_shift_var0, hu0nat n g]
  have et : ∀ n' (g' : Hom n' n) r, (Cof.restr (Cof.restr (ival ρ φ).face g) g').holds →
      tubeV S (.app u.shift (.var 0)) (ρ.restr g) (TEnv.cons (TEnv.restr γ g) v) n' g' r =
      appV n' (Tube.canon (ival ρ φ).face (tubeV S u ρ γ) n' (g.comp g') r) (res g' v) := by
    intro n' g' r hh
    rw [Cof.restr_restr] at hh
    simp only [tubeV]
    rw [TEnv.restr_cons, sem_app_shift_var0, tube_canon_eq hh, IEnv.restr_restr, TEnv.restr_restr]
    rfl
  have hface : (ival (ρ.restr g) φ).face = Cof.restr (ival ρ φ).face g := by rw [ival.restr, DM.face_restr]
  have hu0' : res g (sem S u0 m ρ γ) ∈ piElSet n (res g (sem S A m ρ γ)) (res g Bf) := by
    rw [El_piC] at hu0; have := res_mem_piElSet hu0 g
    rwa [res_id hAkv, res_id (isKV_famV _ _)] at this
  have hvid : v ∈ El (res g (sem S A m ρ γ)) (Hom.id n) := by rw [El_res, Hom.comp_id]; exact hv
  have hcond : HcompCond S B φ (.app u.shift (.var 0)) (.app u0.shift (.var 0)) n (ρ.restr g)
      (TEnv.cons (TEnv.restr γ g) v) := by
    refine ⟨?_, ?_, ?_, fun k h => ?_, fun k h => ?_⟩
    · rw [eB]; exact ⟨l, hl, Or.inl ⟨(hfamW n g v hv).2, (hfamW n g v hv).1⟩⟩
    · rw [eB, eb, hface]
      exact (hut.congr ((isCof_ival_face ρ φ).restr g) fun n' g' r hh => (et n' g' r hh).symm)
    · rw [eB, eb]; exact hb
    · have hv2 : res h v ∈ El (sem S A m ρ γ) (g.comp h) := hAfib.elRes _ _ v hv _ h
      rw [IEnv.restr_restr, TEnv.restr_cons, TEnv.restr_restr, eB, hfam.coh n g v hv k h]
      exact (apZ_dat_famV (sem S A m ρ γ) (fun k f a => sem S B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a))
        (g.comp h) hv2).symm
    · rw [IEnv.restr_restr, TEnv.restr_cons, TEnv.restr_restr, sem_app_shift_var0, eb, hu0nat k (g.comp h),
        res_appV hu0' hvid h, res_res]
  rw [sem_hcomp hcond, eB, eb, hface]
  exact hcompAt_congr et

theorem sem_dsubst (t : Tm) (τ : ℕ → I) (ρ : IEnv m) (γ : ℕ → V) :
    sem S (t.dsubst τ) m ρ γ = sem S t m (fun i => ival ρ (τ i)) γ := by
  rw [Tm.dsubst, sem_subst S t m ρ γ _ _ (fun x => natural_var S x ρ γ)]; rfl

/-- A point of the form `⟦A⟧(ρ.ext, γ.wk)` of a natural line is the same as the line. -/
theorem papp_dshift_var0_generic {p : Tm} {ρ : IEnv m} {γ : ℕ → V} {P : V} (hnat : Natural S p m ρ γ)
    (hP : sem S p m ρ γ = pathOfLine m P) (hPkv : IsKV (m + 1) P) :
    sem S (.papp p.dshift (.var 0)) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) = P ∧
      Natural S (.papp p.dshift (.var 0)) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) := by
  have hb := sem_eta_body hnat hP
  have h2 := hb (m + 1) (Hom.id (m + 1))
  rw [IEnv.restr_id, TEnv.restr_id_of_kv (γ := TEnv.restr γ (Hom.wk m)) (fun x => isKV_res _ _),
    res_id hPkv] at h2
  exact ⟨h2, fun k g => by rw [hb k g, h2]⟩

/-! ### hcompIPi -/

theorem sem_hcompIPi {A u u0 : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V}
    (hc : HcompCond S (.ipi A) φ u u0 m ρ γ) :
    sem S (Tm.hcompIPi A φ u u0) m ρ γ = sem S (.hcomp (.ipi A) φ u u0) m ρ γ := by
  obtain ⟨hN, hL, hsem, l, hl, hV, hW⟩ := (show TyOK S (.ipi A) m ρ γ from hc.1).ipi_at
  have hLfib := hW.fib
  have hp0 := hc.2.2.1
  have hu := hc.2.1
  have hu0nat := hc.2.2.2.2
  rw [hsem] at hp0 hu
  have hφ := isCof_ival_face ρ φ
  obtain ⟨hp0eq, hline⟩ := ipi_line hLfib hp0
  rw [Hom.lift_id] at hline
  have hP := papp_dshift_var0_generic hu0nat hp0eq (hLfib.elKV _ _ _ hline)
  have hface : (ival ρ.ext φ.shift).face = Cof.restr (ival ρ φ).face (Hom.wk m) := by
    rw [ival_shift]; exact face_ival_restr ρ φ (Hom.wk m)
  have et : ∀ n (h : Hom n (m + 1)) r, (Cof.restr (Cof.restr (ival ρ φ).face (Hom.wk m)) h).holds →
      tubeV S (.papp (u.dsubst fun | 0 => .var 0 | n + 1 => .var (n + 2)) (.var 1)) ρ.ext
        (TEnv.restr γ (Hom.wk m)) n h r = ipiHTube (Tube.canon (ival ρ φ).face (tubeV S u ρ γ)) n h r := by
    intro n h r hh
    rw [Cof.restr_restr] at hh
    simp only [tubeV, ipiHTube, sem_papp, sem_dsubst, tube_canon_eq hh, TEnv.restr_restr]
    congr 2
    funext i; cases i with
    | zero => rfl
    | succ i => simp [IEnv.cons, IEnv.restr, IEnv.ext, DM.restr_restr]
  have hcb : HcompCond S A φ.shift (.papp (u.dsubst fun | 0 => .var 0 | n + 1 => .var (n + 2)) (.var 1))
      (.papp u0.dshift (.var 0)) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) := by
    refine ⟨⟨l, hl, Or.inl ⟨hW, hV⟩⟩, ?_, ?_, hN, hP.2⟩
    · rw [hP.1, hface]
      have := ipiHTube_ok hLfib hφ hp0 hu
      rw [Hom.lift_id] at this
      exact this.congr (hφ.restr _) fun n h r hh => (et n h r hh).symm
    · rw [hP.1]; exact hline
  rw [sem_hcomp hc, hsem, hcompAt_ipiC hp0 hu, hcompIPiF_eq, Hom.lift_id]
  have e1 : sem S (Tm.hcompIPi A φ u u0) m ρ γ = pathOfLine m (lineV S (.hcomp A φ.shift
      (.papp (u.dsubst fun | 0 => .var 0 | n + 1 => .var (n + 2)) (.var 1)) (.papp u0.dshift (.var 0))) m ρ γ) :=
    sem_plam hcb.natural
  rw [e1]
  unfold lineV
  rw [sem_hcomp hcb, hP.1, hface]
  congr 1
  exact hcompAt_congr et

/-! ### transpIPi -/

theorem ConstOn.res_id {c : V} {f : Hom (n + 1) m} {φ : Cof n} (h : ConstOn c f φ) :
    ConstOn (res f c) (Hom.id (n + 1)) φ := by
  intro n' g hg r
  rw [res_res, res_res, Hom.id_comp, Hom.id_comp]; exact h n' g hg r

/-- The interval environment of the swapped line, at the doubly generic point. -/
theorem ext_ext_swap (ρ : IEnv m) :
    (fun i => ival (ρ.ext.ext) ((fun | 0 => I.var 1 | 1 => I.var 0 | n + 2 => I.var (n + 2) : ℕ → I) i)) =
      ρ.ext.ext.restr (swapHom m) := by
  funext i
  rcases i with _ | _ | i
  · ext p; simp [IEnv.ext, IEnv.restr, swapHom, iVar, Hom.snoc, Hom.app, Hom.wk]
  · ext p; simp [IEnv.ext, IEnv.restr, swapHom, jVar, Hom.snoc, Hom.app, Hom.wk]
  · simp only [ival.var, IEnv.ext, IEnv.restr, DM.restr_restr]
    congr 1
    simp only [swapHom, Hom.comp_assoc, Hom.wk_comp_snoc]

theorem wk_wk_swap : (Hom.wk m).comp ((Hom.wk (m + 1)).comp (swapHom m)) = (Hom.wk m).comp (Hom.wk (m + 1)) := by
  simp only [swapHom, Hom.wk_comp_snoc]

theorem sem_transpIPi {A u0 : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V}
    (hc : TranspCond S (.ipi A) φ u0 m ρ γ) :
    sem S (Tm.transpIPi A φ u0) m ρ γ = sem S (.transp (.ipi A) φ u0) m ρ γ := by
  obtain ⟨hN2, hL2, hsem, l, hl, hV, hW⟩ := (show TyOK S (.ipi A) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) from hc.1).ipi_at
  set L2 := lineV S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))
  have hLfib := hW.fib
  have hcon := hc.2.1
  have hp0 := hc.2.2.1
  have hu0nat := hc.2.2.2.2
  unfold lineV at hcon hp0
  rw [hsem] at hcon hp0
  have hφ := isCof_ival_face ρ φ
  have hp0' : sem S u0 m ρ γ ∈ El (ipiC (m + 1) L2) ((Hom.id (m + 1)).comp (Hom.endpt m (DM.zero m))) := hp0
  obtain ⟨hp0eq, -⟩ := ipi_line hLfib hp0'
  have hline := ipi_base_mem hLfib hp0'
  rw [Hom.lift_id, Hom.id_comp] at hline
  have hP := papp_dshift_var0_generic hu0nat hp0eq (hLfib.elKV _ _ _ (ipi_line hLfib hp0').2)
  have hface : (ival ρ.ext φ.shift).face = Cof.restr (ival ρ φ).face (Hom.wk m) := by
    rw [ival_shift]; exact face_ival_restr ρ φ (Hom.wk m)
  set A' := A.dsubst (fun | 0 => I.var 1 | 1 => I.var 0 | n + 2 => I.var (n + 2) : ℕ → I)
  have hγs : TEnv.restr (TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.wk (m + 1))) (swapHom m) =
      TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.wk (m + 1)) := by
    rw [TEnv.restr_restr, TEnv.restr_restr, TEnv.restr_restr, wk_wk_swap]
  have eL : ∀ k (g : Hom k (m + 2)),
      sem S A' k (ρ.ext.ext.restr g) (TEnv.restr (TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.wk (m + 1))) g) =
        res g (res (swapHom m) L2) := by
    intro k g
    have e1 : (fun i => ival (ρ.ext.ext.restr g)
        ((fun | 0 => I.var 1 | 1 => I.var 0 | n + 2 => I.var (n + 2) : ℕ → I) i)) =
        ρ.ext.ext.restr ((swapHom m).comp g) := by
      rw [← IEnv.restr_restr, ← ext_ext_swap]; rfl
    rw [sem_dsubst, e1, ← hγs, TEnv.restr_restr, hN2 k, res_res]
  have eL0 : lineV S A' (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) = res (swapHom m) L2 := by
    have := eL (m + 2) (Hom.id (m + 2))
    rwa [IEnv.restr_id, TEnv.restr_id_of_kv (γ := TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.wk (m + 1)))
      (fun x => isKV_res _ _), res_id (isKV_res _ _)] at this
  have tc : TranspCond S A' φ.shift (.papp u0.dshift (.var 0)) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) := by
    refine ⟨?_, ?_, ?_, fun k g => ?_, hP.2⟩
    · rw [eL0]; exact ⟨l, hl, Or.inl ⟨hW.res _, res_mem_Vt hV _⟩⟩
    · rw [eL0, hface]
      have := ipi_constOn hcon
      rw [Hom.lift_id, Hom.id_comp] at this
      exact this.res_id
    · rw [eL0, hP.1, El_res, Hom.id_comp]; exact hline
    · exact (eL k g).trans (by rw [← eL0])
  have e1 : sem S (Tm.transpIPi A φ u0) m ρ γ =
      pathOfLine m (lineV S (.transp A' φ.shift (.papp u0.dshift (.var 0))) m ρ γ) := sem_plam tc.natural
  rw [e1, sem_transp hc]
  unfold lineV
  rw [sem_transp tc, eL0, hP.1, hface, transpAt_res, Hom.comp_id]
  show _ = transpAt (sem S (Tm.ipi A) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) _ _ _
  rw [hsem, transpAt_ipiC hLfib hp0', transpIPiF_eq, Hom.lift_id, Hom.id_comp]

/-! ### hcompPath -/

theorem face_ival_or (ρ : IEnv m) (x y : I) :
    (ival ρ (.or x y)).face = Cof.or (ival ρ x).face (ival ρ y).face := by
  ext p; simp only [Cof.or, DM.face, Set.mem_union, Set.mem_setOf_eq, ival.fn, I.eval]
  constructor
  · rintro ⟨hp, h⟩
    rcases (M4.join_eq_one_K3 (ival_isK3 ρ x hp) (ival_isK3 ρ y hp)).1 h with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, h⟩
  · rintro (⟨hp, h⟩ | ⟨hp, h⟩) <;> refine ⟨hp, ?_⟩ <;> simp [h]

theorem face_ival_neg (ρ : IEnv m) (x : I) : (ival ρ (.neg x)).face = Cof.eq0 (ival ρ x) := rfl

theorem face_ival_var (ρ : IEnv m) (i : ℕ) : (ival ρ (.var i)).face = Cof.eq1 (ρ i) := rfl

theorem holds_ival_iff_face (ρ : IEnv m) (x : I) : (ival ρ x).holds ↔ Cof.holds (ival ρ x).face :=
  DM.holds_iff_face_holds _

/-- `a` and `b` of a natural, good path type are natural. -/
theorem natural_path_ends {A a b : Tm} {ρ : IEnv m} {γ : ℕ → V} (hty : TyOK S (.path A a b) m ρ γ)
    (hnat : Natural S (.path A a b) m ρ γ) : Natural S a m ρ γ ∧ Natural S b m ρ γ := by
  obtain ⟨-, hL, ha, hb, hsem, -⟩ := hty.path_at
  have key : ∀ k (g : Hom k m), sem S a k (ρ.restr g) (TEnv.restr γ g) = res g (sem S a m ρ γ) ∧
      sem S b k (ρ.restr g) (TEnv.restr γ g) = res g (sem S b m ρ γ) := by
    intro k g
    have hty' : TyOK S (.path A a b) k (ρ.restr g) (TEnv.restr γ g) := by
      unfold TyOK; rw [hnat k g]; exact hty.res g
    obtain ⟨-, hL', ha', hb', hsem', -⟩ := hty'.path_at
    have := hnat k g
    rw [hsem', hsem, res_pathC] at this
    have := pathC_inj hL' ha' hb' (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) this
    exact ⟨this.2.1, this.2.2⟩
  exact ⟨fun k g => (key k g).1, fun k g => (key k g).2⟩

theorem sem_hcompPath {A a b u p0 : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V}
    (hc : HcompCond S (.path A a b) φ u p0 m ρ γ) :
    sem S (Tm.hcompPath A a b φ u p0) m ρ γ = sem S (.hcomp (.path A a b) φ u p0) m ρ γ := by
  have hty : TyOK S (.path A a b) m ρ γ := hc.1
  obtain ⟨hN, hL, ha, hb, hsem, l, hl, hV, hW, ha0, ha1⟩ := hty.path_at
  obtain ⟨hanat, hbnat⟩ := natural_path_ends hty hc.2.2.2.1
  have hLfib := hW.fib
  have hp0 := hc.2.2.1
  have hu := hc.2.1
  have hp0nat := hc.2.2.2.2
  rw [hsem] at hp0 hu
  have hφ := isCof_ival_face ρ φ
  set L := lineV S A m ρ γ
  set a0 := sem S a m ρ γ
  set a1 := sem S b m ρ γ
  obtain ⟨hp0eq, hline, -, -⟩ := path_line hLfib hp0
  rw [Hom.lift_id] at hline
  have hP := papp_dshift_var0_generic hp0nat hp0eq (hLfib.elKV _ _ _ hline)
  set ins1 : ℕ → I := fun | 0 => .var 0 | n + 1 => .var (n + 2)
  set sys := Tm.split φ.shift.shift (.papp (u.dsubst ins1) (.var 1)) (.or (.neg (.var 1)) (.var 1))
    (.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)
  have hface : (ival ρ.ext (.or φ.shift (.or (.neg (.var 0)) (.var 0)))).face = pathFace (ival ρ φ).face := by
    rw [face_ival_or, face_ival_or, face_ival_neg, face_ival_var, ival_shift]
    unfold pathFace
    rw [show ρ.ext.tail = ρ.restr (Hom.wk m) from rfl, face_ival_restr]; rfl
  have et : ∀ n (h : Hom n (m + 1)) r, ((pathFace (ival ρ φ).face).restr h).holds →
      tubeV S sys ρ.ext (TEnv.restr γ (Hom.wk m)) n h r =
        pathHTube (ival ρ φ).face (Tube.canon (ival ρ φ).face (tubeV S u ρ γ)) a0 a1 n h r := by
    intro n h r hh
    set env := (ρ.ext.restr h).cons r
    set γ' := TEnv.restr (TEnv.restr γ (Hom.wk m)) h
    have htt : env.tail.tail = (ρ.restr (Hom.wk m)).restr h := rfl
    have hφ2 : (ival env φ.shift.shift).holds ↔ (Cof.restr (ival ρ φ).face ((Hom.wk m).comp h)).holds := by
      rw [ival_shift, ival_shift, htt, IEnv.restr_restr, holds_face_restr_iff]
    have hv1 : env 1 = (lastVar m).restr h := rfl
    have h0iff : (ival env (.neg (.var 1))).holds ↔ ((Cof.eq0 (lastVar m)).restr h).holds := by
      rw [holds_ival_iff_face, face_ival_neg, ival.var, hv1, Cof.eq0_restr]
    have h1iff : (ival env (.var 1)).holds ↔ ((Cof.eq1 (lastVar m)).restr h).holds := by
      rw [holds_ival_iff_face, face_ival_var, hv1, Cof.eq1_restr]
    have hγ' : γ' = TEnv.restr γ ((Hom.wk m).comp h) := TEnv.restr_restr _ _ _
    have eA : sem S a.dshift.dshift n env γ' = res ((Hom.wk m).comp h) a0 := by
      rw [sem_dshift_tail, sem_dshift_tail, htt, IEnv.restr_restr, hγ', hanat]
    have eB : sem S b.dshift.dshift n env γ' = res ((Hom.wk m).comp h) a1 := by
      rw [sem_dshift_tail, sem_dshift_tail, htt, IEnv.restr_restr, hγ', hbnat]
    have eT : sem S (.papp (u.dsubst ins1) (.var 1)) n env γ' =
        pappV n (tubeV S u ρ γ n ((Hom.wk m).comp h) r) ((lastVar m).restr h) := by
      rw [sem_papp, sem_dsubst, ival.var, hv1, hγ']
      simp only [tubeV]
      congr 2
      funext i; cases i with
      | zero => rfl
      | succ i => simp [env, ins1, IEnv.cons, IEnv.restr, IEnv.ext, DM.restr_restr]
    have hne01 : ¬ (((Cof.eq0 (lastVar m)).restr h).holds ∧ ((Cof.eq1 (lastVar m)).restr h).holds) := by
      rintro ⟨h0, h1⟩
      exact DM.zero_ne_one' ((lastVar_zero_of h0).symm.trans (lastVar_one_of h1))
    have eU0 : ((Cof.eq0 (lastVar m)).restr h).holds →
        sem S (.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift) n env γ' =
          res ((Hom.wk m).comp h) a0 := by
      intro h0
      rw [sem_split (Or.inl (h0iff.2 h0)) (fun _ h1 => absurd ⟨h0, h1iff.1 h1⟩ hne01),
        if_pos (h0iff.2 h0), eA]
    have eU1 : ((Cof.eq1 (lastVar m)).restr h).holds →
        sem S (.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift) n env γ' =
          res ((Hom.wk m).comp h) a1 := by
      intro h1
      rw [sem_split (Or.inr (h1iff.2 h1)) (fun h0 _ => absurd ⟨h0iff.1 h0, h1⟩ hne01),
        if_neg (fun h0 => hne01 ⟨h0iff.1 h0, h1⟩), eB]
    have hψ : (ival env (.or (.neg (.var 1)) (.var 1))).holds ↔
        ((Cof.eq0 (lastVar m)).restr h).holds ∨ ((Cof.eq1 (lastVar m)).restr h).holds := by
      rw [holds_ival_iff_face, face_ival_or, Cof.holds_or, ← holds_ival_iff_face, ← holds_ival_iff_face,
        h0iff, h1iff]
    simp only [tubeV]
    unfold pathHTube
    by_cases h1 : (Cof.restr (ival ρ φ).face ((Hom.wk m).comp h)).holds
    · have hm := hu.mem n _ r h1
      rw [Hom.id_comp] at hm
      obtain ⟨q, -, hq, hq0, hq1⟩ := mem_pathC.1 hm
      have hover : (ival env (.or (.neg (.var 1)) (.var 1))).holds →
          sem S (.papp (u.dsubst ins1) (.var 1)) n env γ' =
            sem S (.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift) n env γ' := by
        intro hψh
        rw [eT, hq, pappV_pathOfLine]
        rcases hψ.1 hψh with h0 | h1'
        · rw [eU0 h0, lastVar_zero_of h0, hq0]
        · rw [eU1 h1', lastVar_one_of h1', hq1]
      rw [sem_split (Or.inl (hφ2.2 h1)) (fun _ => hover), if_pos (hφ2.2 h1), if_pos h1, eT,
        tube_canon_eq h1]
    · have hcases := pathFace_cases hh
      rw [sem_split (Or.inr ?_) (fun h => absurd (hφ2.1 h) h1), if_neg (fun h => h1 (hφ2.1 h)), if_neg h1]
      · by_cases h0 : ((Cof.eq0 (lastVar m)).restr h).holds
        · rw [if_pos h0, eU0 h0]
        · rw [if_neg h0]
          have h1' : ((Cof.eq1 (lastVar m)).restr h).holds := by
            rcases hcases with h3 | h3 | h3
            · exact absurd h3 h1
            · exact absurd (eq0_restr_holds_iff.2 h3) h0
            · rw [Cof.eq1_restr, h3, Cof.eq1_one]; exact Cof.holds_top
          rw [eU1 h1']
      · rcases hcases with h3 | h3 | h3
        · exact absurd h3 h1
        · exact hψ.2 (Or.inl (eq0_restr_holds_iff.2 h3))
        · exact hψ.2 (Or.inr (by rw [Cof.eq1_restr, h3, Cof.eq1_one]; exact Cof.holds_top))
  have hcb : HcompCond S A (.or φ.shift (.or (.neg (.var 0)) (.var 0))) sys (.papp p0.dshift (.var 0))
      (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) := by
    refine ⟨⟨l, hl, Or.inl ⟨hW, hV⟩⟩, ?_, ?_, hN, hP.2⟩
    · rw [hP.1, hface]
      have := pathHTube_ok hLfib ha0 ha1 hφ hp0 hu
      rw [Hom.lift_id, res_id ha, res_id hb] at this
      exact this.congr (isCof_pathFace hφ) fun n h r hh => (et n h r hh).symm
    · rw [hP.1]; exact hline
  have e1 : sem S (Tm.hcompPath A a b φ u p0) m ρ γ = pathOfLine m (lineV S (.hcomp A
      (.or φ.shift (.or (.neg (.var 0)) (.var 0))) sys (.papp p0.dshift (.var 0))) m ρ γ) :=
    sem_plam hcb.natural
  rw [e1, sem_hcomp hc, hsem, hcompAt_pathC hp0 hu, hcompPathF_eq, Hom.lift_id, res_id ha, res_id hb]
  unfold lineV
  rw [sem_hcomp hcb, hP.1, hface]
  congr 1
  exact hcompAt_congr et

/-! ### transpFill -/

theorem bind2_and_env (ρ : IEnv m) :
    (fun i => ival ρ.ext.ext (Tm.bind2 (.and (.var 1) (.var 0)) i)) = ρ.ext.restr (tfLine m) := by
  funext i
  rcases i with _ | i
  · ext p; simp [Tm.bind2, IEnv.ext, IEnv.restr, tfLine, iVar, jVar, I.eval, Hom.snoc, Hom.app, Hom.wk]
  · simp only [Tm.bind2, ival.var, IEnv.ext, IEnv.restr, DM.restr_restr]
    congr 1
    simp only [tfLine, Hom.wk_comp_snoc]

theorem face_fill (ρ : IEnv m) (φ : I) :
    (ival ρ.ext (.or φ.shift (.neg (.var 0)))).face = fillFace (ival ρ φ).face := by
  rw [face_ival_or, face_ival_neg, ival_shift, show ρ.ext.tail = ρ.restr (Hom.wk m) from rfl,
    face_ival_restr]
  rfl

theorem transpFill_cond {A a : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V} (hc : TranspCond S A φ a m ρ γ) :
    TranspCond S (A.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.or φ.shift (.neg (.var 0))) a.dshift
        (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) ∧
      sem S (Tm.transpFill A φ a) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) =
        transpFillF (lineV S A m ρ γ) (Hom.id (m + 1)) (ival ρ φ).face (sem S a m ρ γ) := by
  obtain ⟨hty, hcon, ha, hN, han⟩ := hc
  have hfib := hty.fib
  have hφ := isCof_ival_face ρ φ
  have hwt : (Hom.wk m).comp (tfLine m) = (Hom.wk m).comp (Hom.wk (m + 1)) := by
    simp only [tfLine, Hom.wk_comp_snoc]
  have hγt : ∀ k (g : Hom k (m + 2)), TEnv.restr (TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.wk (m + 1))) g =
      TEnv.restr (TEnv.restr γ (Hom.wk m)) ((tfLine m).comp g) := by
    intro k g
    rw [TEnv.restr_restr, TEnv.restr_restr, TEnv.restr_restr, ← Hom.comp_assoc (Hom.wk m) (tfLine m) g, hwt]; rfl
  have eL : ∀ k (g : Hom k (m + 2)),
      sem S (A.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) k (ρ.ext.ext.restr g)
        (TEnv.restr (TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.wk (m + 1))) g) =
        res g (res (tfLine m) (lineV S A m ρ γ)) := by
    intro k g
    have e1 : (fun i => ival (ρ.ext.ext.restr g) (Tm.bind2 (.and (.var 1) (.var 0)) i)) =
        ρ.ext.restr ((tfLine m).comp g) := by
      rw [← IEnv.restr_restr, ← bind2_and_env]; rfl
    rw [sem_dsubst, e1, hγt, hN k, res_res]
  have eL0 : lineV S (A.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) =
      res (tfLine m) (lineV S A m ρ γ) := by
    have := eL (m + 2) (Hom.id (m + 2))
    rwa [IEnv.restr_id, TEnv.restr_id_of_kv (γ := TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.wk (m + 1)))
      (fun x => isKV_res _ _), res_id (isKV_res _ _)] at this
  have eb : sem S a.dshift (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) = res (Hom.wk m) (sem S a m ρ γ) := by
    rw [sem_dshift, han]
  rw [Hom.id_comp] at ha
  have tc : TranspCond S (A.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.or φ.shift (.neg (.var 0))) a.dshift
      (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) := by
    refine ⟨?_, ?_, ?_, fun k g => (eL k g).trans (by rw [← eL0]), han.dshift⟩
    · rw [eL0]; exact hty.res _
    · rw [eL0, face_fill]
      have := constOn_tfLine hfib hφ hcon (by rw [Hom.id_comp]; exact ha)
      rw [Hom.id_comp] at this; exact this.res_id
    · rw [eL0, eb, El_res, Hom.id_comp]
      have := tf_base hfib hφ hcon (by rw [Hom.id_comp]; exact ha)
      rwa [Hom.id_comp] at this
  refine ⟨tc, ?_⟩
  rw [Tm.transpFill, sem_transp tc, eL0, eb, face_fill, transpAt_res, Hom.comp_id, transpFillF, Hom.id_comp]

end

end Model
