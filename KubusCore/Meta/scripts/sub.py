import sys, re
sys.path.insert(0,'/home/agent/code/kubus-meta/KubusCore/Meta/scripts')
from rules import parse, split_top
SB = "Tm.subst, I.subst, inst_subst, dinst_subst, equiv_subst, dshift_dup_subst, shift_up_subst, Ishift_up_subst, Tm.up, I.up, List.map_nil"
def S(x): return f"(by simpa only [{SB}] using {x})"
def T(h, R="hσ"): return f"((sub_ty hS {h}).2.1 {R})"
def E(h, R="hσ"): return f"((sub_eq hS {h}).2 {R})"
def ST(h, R="hσ"): return S(T(h,R)[1:-1])
def SE(h, R="hσ"): return S(E(h,R)[1:-1])
def F(h, a="k1", b="k2", e="kE"): return f"((sub_ty hS {h}).2.2 {a} {b} {e})"
def SF(h, a="k1", b="k2", e="kE"): return S(F(h,a,b,e)[1:-1])
WF = "hσ.wf"
ENT = lambda h: f"(ent_trans hσ.ent (ent_subst {h} _))"
UPC = lambda h, k='ty': f"(hσ.upC hS (sub_{k} hS {h}).1)"
DUP = "(hσ.dup hS)"
CL0 = "(fun _ h => absurd h (Nat.not_lt_zero _))"
PARAMS = "(fun k A hk => by simpa using hS.params _ _ _ _ h0 hk)"

sub = {}
sub['HasTy0'] = {
'var': "by simp only [Tm.subst]; exact hσ.look _ _ h1",
'conv': f"HasTy0.conv {T('h0')} {E('h1')}",
'restrict': "(sub_ty hS h2).2.1 (hσ.restrictSrc h1)",
'const': f"by obtain ⟨_, hA⟩ := hS.defn _ _ _ h1; rw [closed_subst_id hA {CL0} {CL0}]; exact HasTy0.const {WF} h1",
'univ': f"HasTy0.univ h0 {WF}",
'cumul': f"HasTy0.cumul h0 {T('h1')}",
'pi': f"by simp only [{SB}]; exact HasTy0.pi {T('h0')} {T('h1',UPC('h1'))}",
'lam': f"by simp only [{SB}]; exact HasTy0.lam {ST('h0')} {T('h1',UPC('h1'))}",
'app': f"by simp only [{SB}]; exact HasTy0.app {ST('h0')} {T('h1')}",
'sigma': f"by simp only [{SB}]; exact HasTy0.sigma {T('h0')} {T('h1',UPC('h1'))}",
'pair': f"by simp only [{SB}]; exact HasTy0.pair {ST('h0')} {T('h1')} {ST('h2')}",
'fst': f"by simp only [{SB}]; exact HasTy0.fst {ST('h0')}",
'snd': f"by simp only [{SB}]; exact HasTy0.snd {ST('h0')}",
'path': f"by simp only [{SB}]; exact HasTy0.path {T('h0',DUP)} {ST('h1')} {ST('h2')}",
'plam': f"by simp only [{SB}]; exact HasTy0.plam {ST('h0')} {T('h1',DUP)} {SE('h2')} {SE('h3')}",
'papp': f"by simp only [{SB}]; exact HasTy0.papp {ST('h0')} (hσ.sc h1)",
'ipi': f"by simp only [{SB}]; exact HasTy0.ipi {WF} {T('h1',DUP)}",
'ilam': f"by simp only [{SB}]; exact HasTy0.ilam {ST('h0')} {T('h1',DUP)}",
'iapp': f"by simp only [{SB}]; exact HasTy0.iapp {ST('h0')} (hσ.sc h1)",
'split': f"by simp only [{SB}]; exact HasTy0.split (hσ.sc h0) (hσ.sc h1) {S(ENT('h2'))} {T('h3')} {T('h4','(hσ.underCof h0)')} {T('h5','(hσ.underCof h1)')} {E('h6','((hσ.underCof h0).underCof h1)')}",
'abort': f"HasTy0.abort {ENT('h0')} {T('h1')}",
'transp': f"by simp only [{SB}]; exact HasTy0.transp {T('h0',DUP)} (hσ.sc h1) {SE('h2','((hσ.underCof h1).dup hS)')} {ST('h3')}",
'hcomp': f"by simp only [{SB}]; exact HasTy0.hcomp {T('h0')} (hσ.sc h1) {ST('h2','((hσ.underCof h1).dup hS)')} {T('h3')} {SE('h4','(hσ.underCof h1)')}",
'glue': f"by simp only [{SB}]; exact HasTy0.glue {T('h0')} (hσ.sc h1) {T('h2','(hσ.underCof h1)')} {ST('h3','(hσ.underCof h1)')}",
'glueEl': f"by have hφ := scoped_cof_right (scoped_of_ty h1); simp only [{SB}]; exact HasTy0.glueEl {ST('h0')} {ST('h1','(hσ.underCof hφ)')} {T('h2','(hσ.underCof hφ)')} {T('h3')} {SE('h4','(hσ.underCof hφ)')}",
'unglue': f"by have hφ := scoped_cof_right (scoped_of_ty h2); simp only [{SB}]; exact HasTy0.unglue {ST('h0')} {T('h1')} {ST('h2','(hσ.underCof hφ)')} {ST('h3')}",
'data': f"by simp only [{SB}]; exact HasTy0.data h0 h1 (((sub_tele hS h2).2 {PARAMS}).1 hσ)",
'con': f"""by
      have hlen := tele_length h4
      have ht := ((sub_tele hS h5).2 (fun k A hk => by
        rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h1 k A hk)).1 hσ
      simp only [{SB}]
      refine HasTy0.con h0 h1 (isList_subst h2 _ _) {T('h3')} (((sub_tele hS h4).2 {PARAMS}).1 hσ) ?_
        (by simpa using h6) (fun r hr => ?_)
      · rw [toList_subst h2, ← List.map_reverse]; exact ht
      · obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr; exact hσ.sc (h7 r0 hr0)""",
'elim': f"""by
      have hlen := tele_length h3
      simp only [{SB}]
      refine HasTy0.elim h0 (isList_subst h1 _ _) {T('h2')} (((sub_tele hS h3).2 {PARAMS}).1 hσ)
        {T('h4',UPC('h4'))} (isList_subst h5 _ _)
        (by rw [toList_subst h5, List.length_map, h6]) ?_ ?_ {T('h9')}
      · intro c C b hc hb
        rw [toList_subst h5, List.getElem?_map] at hb
        obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
        have := (sub_ty hS (h7 c C b0 hc hb0)).2.1 hσ
        rwa [branchTy_subst _ _ hS h0 hc h1 hlen] at this
      · intro c C b k ψ e hc hb hk
        rw [toList_subst h5, List.getElem?_map] at hb
        obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
        have hψ := hS.bnd _ _ _ _ _ _ _ h0 hc hk
        have := (sub_eq hS (h8 c C b0 k ψ e hc hb0 hk)).2
          (hσ.branch hS h0 hc h1 hlen hψ.1 (sub_eq hS (h8 c C b0 k ψ e hc hb0 hk)).1)
        rw [branchApp_subst, bndElim_subst _ _ h1 hlen h5 e hψ.2, branchBody_subst] at this
        exact this""",
}

def UP2(h, k='ty'): return f"obtain ⟨u1, u2, uE⟩ := TySub.up2 hS k1 k2 kE (sub_{k} hS {h}).1"
DUP3 = "(k1.dup hS) (k2.dup hS) (kE.dup hS)"
def CONV2(hpremise):  # hsub k2 converted to the σ1-type via the functionality of the type premise
    return f"(HasTy0.conv (hsub k2) (EqTm0.symm {F(hpremise)}))"
def COF3(hφ, hφ12):
    return f"(k1.underCof {hφ}) (k2.underCofE (k1.sc {hφ}) {hφ12}) (kE.underCof k1.hscoped (k1.sc {hφ}))"
fun = {}
fun['HasTy0'] = {
'var': "kE.1 _ _ h1",
'conv': f"EqTm0.conv {F('h0')} ((sub_eq hS h1).2 k1)",
'restrict': "(sub_ty hS h2).2.2 (k1.restrictSrc h1) (k2.restrictSrc h1) kE",
'const': "EqTm0.refl (hsub k1)",
'univ': "EqTm0.refl (hsub k1)",
'cumul': f"EqTm0.cumul h0 {F('h1')}",
'pi': f"by {UP2('h1')}; exact EqTm0.pi {F('h0')} {F('h1','u1','u2','uE')}",
'sigma': f"by {UP2('h1')}; exact EqTm0.sigma {F('h0')} {F('h1','u1','u2','uE')}",
'lam': f"""by
      {UP2('h1')}
      obtain ⟨_, _, hA, _, _⟩ := (sub_ty hS h1).1
      exact lam_congr' hS (hA k1) {T('h0','k1')} {CONV2('h0')} {F('h1','u1','u2','uE')}""",
'app': f"by simp only [inst_subst]; exact EqTm0.app {F('h0')} {F('h1')}",
'pair': f"by exact EqTm0.pair {T('h0','k1')} {F('h1')} {SF('h2')}",
'fst': f"EqTm0.fst {F('h0')}",
'snd': f"by simp only [inst_subst, Tm.subst]; exact EqTm0.snd {F('h0')}",
'path': f"by simp only [{SB}]; exact EqTm0.path {F('h0','(k1.dup hS)','(k2.dup hS)','(kE.dup hS)')} {SF('h1')} {SF('h2')}",
'plam': f"by exact EqTm0.plam {T('h0','k1')} (hsub k1) {CONV2('h0')} {F('h1','(k1.dup hS)','(k2.dup hS)','(kE.dup hS)')}",
'papp': f"by simp only [{SB}]; exact EqTm0.papp {SF('h0')} (k1.sc h1) (k2.sc h1) (I_eq_subst_scoped h1 kE.2)",
'ipi': f"EqTm0.ipi k1.wf {F('h1','(k1.dup hS)','(k2.dup hS)','(kE.dup hS)')}",
'ilam': f"by exact EqTm0.ilam {T('h0','k1')} {F('h1','(k1.dup hS)','(k2.dup hS)','(kE.dup hS)')}",
'iapp': f"by simp only [{SB}]; exact EqTm0.iapp {SF('h0')} (k1.sc h1) (k2.sc h1) (I_eq_subst_scoped h1 kE.2)",
'split': f"""by
      have hφ12 := eq_ent (I_eq_subst_scoped h0 kE.2)
      have hψ12 := eq_ent (I_eq_subst_scoped h1 kE.2)
      have hL := hsub k1
      have hR := {CONV2('h3')}
      refine EqTm0.local (k1.sc h0) (k1.sc h1) (ent_trans k1.ent (ent_subst h2 _)) hL hR ?_ ?_
      · have hs : (cof Φ' (φ.subst τ1)).Scoped Ψ' := ⟨k1.hscoped, k1.sc h0⟩
        have e1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hs (ent_and_left _ _) hL)
        have e2 := EqTm0.splitL (ent_trans (ent_and_right _ _) hφ12) (HasTy0.restrict hs (ent_and_left _ _) hR)
        have e3 := (sub_ty hS h4).2.2 {COF3('h0','hφ12')}
        exact EqTm0.trans e1 (EqTm0.trans e3 (EqTm0.symm e2))
      · have hs : (cof Φ' (ψ.subst τ1)).Scoped Ψ' := ⟨k1.hscoped, k1.sc h1⟩
        have e1 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hs (ent_and_left _ _) hL)
        have e2 := EqTm0.splitR (ent_trans (ent_and_right _ _) hψ12) (HasTy0.restrict hs (ent_and_left _ _) hR)
        have e3 := (sub_ty hS h5).2.2 {COF3('h1','hψ12')}
        exact EqTm0.trans e1 (EqTm0.trans e3 (EqTm0.symm e2))""",
'abort': "EqTm0.refl (hsub k1)",
'transp': f"""by
      have hφ12 := eq_ent (I_eq_subst_scoped h1 kE.2)
      have hφ21 := eq_ent (I_eq_subst_scoped h1 (fun i hi => I_eq_symm (kE.2 i hi)))
      have hA1 := (sub_ty hS h0).2.2 (k1.inst (r := .one) trivial) (k2.inst (r := .one) trivial) (kE.inst (I_eq_refl _))
      rw [← dinst_one_consI, ← dinst_one_consI] at hA1
      have hT1 := hsub k1
      have hT2 := hsub k2
      simp only [{SB}] at hA1 hT1 hT2 ⊢
      exact EqTm0.transp hT1 (HasTy0.conv hT2 (EqTm0.symm hA1))
        {F('h0','(k1.dup hS)','(k2.dup hS)','(kE.dup hS)')} hφ12 hφ21 {SF('h3')}""",
'hcomp': f"""by
      have hφ12 := eq_ent (I_eq_subst_scoped h1 kE.2)
      have hφ21 := eq_ent (I_eq_subst_scoped h1 (fun i hi => I_eq_symm (kE.2 i hi)))
      have hu := (sub_ty hS h2).2.2 ((k1.underCof h1).dup hS) ((k2.underCofE (k1.sc h1) hφ12).dup hS)
        ((kE.underCof k1.hscoped (k1.sc h1)).dup hS)
      simp only [{SB}] at hu ⊢
      exact EqTm0.hcomp (hsub k1) {CONV2('h0')} {F('h0')} hφ12 hφ21 hu {F('h3')}""",
'glue': f"""by
      have hφ12 := eq_ent (I_eq_subst_scoped h1 kE.2)
      have hφ21 := eq_ent (I_eq_subst_scoped h1 (fun i hi => I_eq_symm (kE.2 i hi)))
      have he := (sub_ty hS h3).2.2 {COF3('h1','hφ12')}
      simp only [{SB}] at he ⊢
      exact EqTm0.glue (hsub k1) (hsub k2) {F('h0')} hφ12 hφ21 ((sub_ty hS h2).2.2 {COF3('h1','hφ12')}) he""",
'glueEl': f"""by
      have hφ := scoped_cof_right (scoped_of_ty h1)
      have hφ12 := eq_ent (I_eq_subst_scoped hφ kE.2)
      have hφ21 := eq_ent (I_eq_subst_scoped hφ (fun i hi => I_eq_symm (kE.2 i hi)))
      have he := (sub_ty hS h1).2.2 {COF3('hφ','hφ12')}
      simp only [{SB}] at he ⊢
      exact EqTm0.glueEl (hsub k1) {CONV2('h0')} hφ12 hφ21 he ((sub_ty hS h2).2.2 {COF3('hφ','hφ12')}) {F('h3')}""",
'unglue': f"""by
      have hφ := scoped_cof_right (scoped_of_ty h2)
      have hφ12 := eq_ent (I_eq_subst_scoped hφ kE.2)
      have hφ21 := eq_ent (I_eq_subst_scoped hφ (fun i hi => I_eq_symm (kE.2 i hi)))
      have he := (sub_ty hS h2).2.2 {COF3('hφ','hφ12')}
      simp only [{SB}] at he ⊢
      exact EqTm0.unglue (hsub k1) {CONV2('h1')} hφ12 hφ21 he {SF('h3')}""",
'data': f"EqTm0.data h0 (hsub k1) (hsub k2) (((sub_tele hS h2).2 {PARAMS}).2 k1 k2 kE)",
'con': f"""by
      have hlen := tele_length h4
      have ht := ((sub_tele hS h5).2 (fun k A hk => by
        rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h1 k A hk)).2 k1 k2 kE
      refine EqTm0.con h0 h1 (hsub k1) {CONV2('h3')} (((sub_tele hS h4).2 {PARAMS}).2 k1 k2 kE) ?_
        (by simp) ?_
      · rw [toList_subst h2, ← List.map_reverse]; exact ht
      · intro k r r' hr hr'
        rw [List.getElem?_map] at hr hr'
        obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.1 hr
        obtain ⟨r0', hr0', rfl⟩ := Option.map_eq_some_iff.1 hr'
        rw [hr0] at hr0'; cases hr0'
        exact I_eq_subst_scoped (h7 r0 (List.mem_of_getElem? hr0)) kE.2""",
'elim': f"""by
      have hlen := tele_length h3
      obtain ⟨_, _, hdata, _, _⟩ := (sub_ty hS h4).1
      {UP2('h4')}
      have hP := (sub_ty hS h4).2.2 (k1.cons {T('h9','k1')}) (k2.cons {T('h9','k2')}) (kE.cons {F('h9')})
      rw [← inst_consT, ← inst_consT] at hP
      have hel1 := hsub k1
      have hel2 := HasTy0.conv (hsub k2) (EqTm0.symm hP)
      simp only [{SB}] at hel1 hel2 ⊢
      refine EqTm0.elim h0 hel1 hel2
        (((sub_tele hS h3).2 {PARAMS}).2 k1 k2 kE) {F('h4','u1','u2','uE')}
        (by rw [toList_subst h5, toList_subst h5, List.length_map, List.length_map]) ?_ {SF('h9')}
      intro c C b b' hc hb hb'
      rw [toList_subst h5, List.getElem?_map] at hb hb'
      obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
      obtain ⟨b0', hb0', rfl⟩ := Option.map_eq_some_iff.1 hb'
      rw [hb0] at hb0'; cases hb0'
      have := (sub_ty hS (h7 c C b0 hc hb0)).2.2 k1 k2 kE
      rwa [branchTy_subst _ _ hS h0 hc h1 hlen] at this""",
}

tele_sub = {
'nil': f"⟨fun hσ => HasTele0.nil hσ.wf, fun k1 k2 kE => EqTele0.nil k1.wf⟩",
'cons': """⟨fun hσ => by
        have hA := tele_closed_head hcl
        have := (sub_ty hS h0).2.1 hσ
        rw [substList_subst hA] at this
        exact HasTele0.cons this (((sub_tele hS h1).2 (tele_closed_tail hcl)).1 hσ),
      fun k1 k2 kE => by
        have hA := tele_closed_head hcl
        have := (sub_ty hS h0).2.2 k1 k2 kE
        rw [substList_subst hA] at this
        exact EqTele0.cons this (((sub_tele hS h1).2 (tele_closed_tail hcl)).2 k1 k2 kE)⟩""",
}
eqtele_sub = {
'nil': "fun hσ => EqTele0.nil hσ.wf",
'cons': """fun hσ => by
        have hA := tele_closed_head hcl
        have := (sub_eq hS h0).2 hσ
        rw [substList_subst hA] at this
        exact EqTele0.cons this ((sub_eqtele hS h1).2 (tele_closed_tail hcl) hσ)""",
'dataInj': f"fun hσ => by simp only [{SB}]; exact EqTele0.dataInj h0 (((sub_tele hS h1).2 {PARAMS}).1 hσ) (((sub_tele hS h2).2 {PARAMS}).1 hσ) {SE('h3')}",
}

def kan(name):
    return f"by rw [{name}_subst]; simp only [{SB}]; exact EqTm0.{name} {ST('h0')}"
eq = {
'refl': f"EqTm0.refl {T('h0')}",
'symm': f"EqTm0.symm {E('h0')}",
'trans': f"EqTm0.trans {E('h0')} {E('h1')}",
'conv': f"EqTm0.conv {E('h0')} {E('h1')}",
'restrict': "(sub_eq hS h2).2 (hσ.restrictSrc h1)",
'cumul': f"EqTm0.cumul h0 {E('h1')}",
'delta': f"""by
      obtain ⟨ht, hA⟩ := hS.defn _ _ _ h1
      rw [closed_subst_id hA {CL0} {CL0}, closed_subst_id ht {CL0} {CL0}]
      have := {T('h0')}
      rw [closed_subst_id hA {CL0} {CL0}] at this
      exact EqTm0.delta this h1""",
'absurd': f"EqTm0.absurd {ENT('h0')} {T('h1')} {T('h2')}",
'local': f"by exact EqTm0.local (hσ.sc h0) (hσ.sc h1) {S(ENT('h2'))} {T('h3')} {T('h4')} {E('h5','(hσ.underCof h0)')} {E('h6','(hσ.underCof h1)')}",
'face': f"""by
      have hΦ := scoped_of_ty h3
      rw [face_dset_subst]
      have hT : TyFace S _ _ _ _ := Or.inr ⟨_, (sub_ty hS h2).2.1,
        face_lemma hΦ (sub_ty hS h2).1 (sub_ty hS h2).2.1 (sub_ty hS h2).2.2 (Or.inl ⟨_, rfl⟩)⟩
      have hf := faceEq_lit (Ψ := Ψ) (ent_trans hσ.ent (ent_subst h1 τ))
      refine face_lemma hΦ (sub_ty hS h3).1 (sub_ty hS h3).2.1 (sub_ty hS h3).2.2 hT hσ
        (hσ.transfer hΦ (sub_ty hS h3).1 (fun j hj => ?_) hf) hf
      by_cases hji : j = i
      · simp only [hji, if_true]; cases d <;> trivial
      · simp only [hji, if_false]; exact hσ.bound j hj""",
'faceU': f"""by
      have hΦ := scoped_of_ty h2
      rw [face_dset_subst]
      have hf := faceEq_lit (Ψ := Ψ) (ent_trans hσ.ent (ent_subst h1 τ))
      refine face_lemma hΦ (sub_ty hS h2).1 (sub_ty hS h2).2.1 (sub_ty hS h2).2.2 (Or.inl ⟨_, rfl⟩) hσ
        (hσ.transfer hΦ (sub_ty hS h2).1 (fun j hj => ?_) hf) hf
      by_cases hji : j = i
      · simp only [hji, if_true]; cases d <;> trivial
      · simp only [hji, if_false]; exact hσ.bound j hj""",
'pi': f"by simp only [{SB}]; exact EqTm0.pi {E('h0')} {E('h1',UPC('h1','eq'))}",
'lam': f"by simp only [{SB}]; exact EqTm0.lam {ST('h0')} {E('h1',UPC('h1','eq'))}",
'app': f"by simp only [{SB}]; exact EqTm0.app {SE('h0')} {E('h1')}",
'sigma': f"by simp only [{SB}]; exact EqTm0.sigma {E('h0')} {E('h1',UPC('h1','eq'))}",
'pair': f"by simp only [{SB}]; exact EqTm0.pair {ST('h0')} {E('h1')} {SE('h2')}",
'fst': f"by simp only [{SB}]; exact EqTm0.fst {SE('h0')}",
'snd': f"by simp only [{SB}]; exact EqTm0.snd {SE('h0')}",
'path': f"by simp only [{SB}]; exact EqTm0.path {E('h0',DUP)} {SE('h1')} {SE('h2')}",
'plam': f"by simp only [{SB}]; exact EqTm0.plam {ST('h0')} {ST('h1')} {ST('h2')} {E('h3',DUP)}",
'papp': f"by simp only [{SB}]; exact EqTm0.papp {SE('h0')} (hσ.sc h1) (hσ.sc h2) (I_eq_subst h3 _)",
'split': f"by have hφ := scoped_cof_right (scoped_of_eq h2); have hψ := scoped_cof_right (scoped_of_eq h3); simp only [{SB}]; exact EqTm0.split {ST('h0')} {ST('h1')} {E('h2','(hσ.underCof hφ)')} {E('h3','(hσ.underCof hψ)')}",
'transp': f"by simp only [{SB}]; exact EqTm0.transp {ST('h0')} {ST('h1')} {E('h2',DUP)} (ent_subst h3 _) (ent_subst h4 _) {SE('h5')}",
'hcomp': f"by have hφ := scoped_cof_shift_right (scoped_of_eq h5); simp only [{SB}]; exact EqTm0.hcomp {ST('h0')} {ST('h1')} {E('h2')} (ent_subst h3 _) (ent_subst h4 _) {SE('h5','((hσ.underCof hφ).dup hS)')} {E('h6')}",
'glue': f"by have hφ := scoped_cof_right (scoped_of_eq h5); simp only [{SB}]; exact EqTm0.glue {ST('h0')} {ST('h1')} {E('h2')} (ent_subst h3 _) (ent_subst h4 _) {E('h5','(hσ.underCof hφ)')} {SE('h6','(hσ.underCof hφ)')}",
'glueEl': f"by have hφ := scoped_cof_right (scoped_of_eq h4); simp only [{SB}]; exact EqTm0.glueEl {ST('h0')} {ST('h1')} (ent_subst h2 _) (ent_subst h3 _) {SE('h4','(hσ.underCof hφ)')} {E('h5','(hσ.underCof hφ)')} {E('h6')}",
'unglue': f"by have hφ := scoped_cof_right (scoped_of_eq h4); simp only [{SB}]; exact EqTm0.unglue {ST('h0')} {ST('h1')} (ent_subst h2 _) (ent_subst h3 _) {SE('h4','(hσ.underCof hφ)')} {SE('h5')}",
'ipi': f"by simp only [{SB}]; exact EqTm0.ipi {WF} {E('h1',DUP)}",
'ilam': f"by simp only [{SB}]; exact EqTm0.ilam {ST('h0')} {E('h1',DUP)}",
'iapp': f"by simp only [{SB}]; exact EqTm0.iapp {SE('h0')} (hσ.sc h1) (hσ.sc h2) (I_eq_subst h3 _)",
'noConf': f"EqTm0.noConf (headClash_subst _ _ h0) {E('h1')} {T('h2')} {T('h3')}",
'piInjDom': f"by simp only [{SB}]; exact EqTm0.piInjDom {SE('h0')}",
'piInjCod': f"by simp only [{SB}]; exact EqTm0.piInjCod {SE('h0')} {T('h1')}",
'sigmaInjDom': f"by simp only [{SB}]; exact EqTm0.sigmaInjDom {SE('h0')}",
'sigmaInjCod': f"by simp only [{SB}]; exact EqTm0.sigmaInjCod {SE('h0')} {T('h1')}",
'pathInjLine': f"by simp only [{SB}]; exact EqTm0.pathInjLine {SE('h0')} (hσ.sc h1)",
'pathInjLeft': f"by simp only [{SB}]; exact EqTm0.pathInjLeft {SE('h0')}",
'pathInjRight': f"by simp only [{SB}]; exact EqTm0.pathInjRight {SE('h0')}",
'ipiInj': f"by simp only [{SB}]; exact EqTm0.ipiInj {SE('h0')} (hσ.sc h1)",
'piBeta': f"by simp only [{SB}]; exact EqTm0.piBeta {ST('h0')}",
'piEta': f"by simp only [{SB}]; exact EqTm0.piEta {ST('h0')}",
'fstBeta': f"by simp only [{SB}]; exact EqTm0.fstBeta {ST('h0')}",
'sndBeta': f"by simp only [{SB}]; exact EqTm0.sndBeta {ST('h0')}",
'sigmaEta': f"by simp only [{SB}]; exact EqTm0.sigmaEta {ST('h0')}",
'pathBeta': f"by simp only [{SB}]; exact EqTm0.pathBeta {ST('h0')}",
'pathEta': f"by simp only [{SB}]; exact EqTm0.pathEta {ST('h0')}",
'ipiEta': f"by simp only [{SB}]; exact EqTm0.ipiEta {ST('h0')}",
'pathZero': f"by simp only [{SB}]; exact EqTm0.pathZero {ST('h0')}",
'pathOne': f"by simp only [{SB}]; exact EqTm0.pathOne {ST('h0')}",
'splitL': f"by simp only [{SB}]; exact EqTm0.splitL {ENT('h0')} {ST('h1')}",
'splitR': f"by simp only [{SB}]; exact EqTm0.splitR {ENT('h0')} {ST('h1')}",
'transpFace': f"by simp only [{SB}]; exact EqTm0.transpFace {ENT('h0')} {ST('h1')}",
'hcompFace': f"by simp only [{SB}]; exact EqTm0.hcompFace {ENT('h0')} {ST('h1')}",
'transpU': f"by simp only [{SB}]; exact EqTm0.transpU {ST('h0')}",
'transpPi': kan('transpPi'), 'transpSigma': kan('transpSigma'), 'transpPath': kan('transpPath'),
'transpIPi': kan('transpIPi'), 'hcompIPi': kan('hcompIPi'), 'hcompPi': kan('hcompPi'),
'hcompSigma': kan('hcompSigma'), 'hcompPath': kan('hcompPath'), 'hcompU': kan('hcompU'),
'hcompGlue': f"by have hφ := scoped_cof_right (scoped_of_ty h2); rw [hcompGlue_subst]; simp only [{SB}]; exact EqTm0.hcompGlue {ST('h0')} {T('h1')} {ST('h2','(hσ.underCof hφ)')}",
'transpGlue': f"""by
      have hφ := scoped_cof_right (scoped_of_ty h2)
      rw [transpGlueWith_subst]; simp only [{SB}]
      exact EqTm0.transpGlue {ST('h0')} {T('h1',DUP)} {ST('h2','((hσ.dup hS).underCof hφ)')}
        (ent_trans (ent_subst h3 _) (forall0_subst _ τ).1)
        (ent_trans (forall0_subst _ τ).2 (ent_subst h4 _))""",
'glueFace': f"by simp only [{SB}]; exact EqTm0.glueFace {ENT('h0')} {ST('h1')}",
'glueElFace': f"by simp only [{SB}]; exact EqTm0.glueElFace {ENT('h0')} {ST('h1')}",
'unglueFace': f"by simp only [{SB}]; exact EqTm0.unglueFace {ENT('h0')} {ST('h1')} {T('h2')} {ST('h3')}",
'glueBeta': f"by simp only [{SB}]; exact EqTm0.glueBeta {ST('h0')} {ST('h1')}",
'glueEta': f"by simp only [{SB}]; exact EqTm0.glueEta {ST('h0')}",
'data': f"by simp only [{SB}]; exact EqTm0.data h0 {T('h1')} {T('h2')} ((sub_eqtele hS h3).2 {PARAMS} hσ)",
'con': f"""by
      obtain ⟨D', C', hD', hC', hps, hlen, _, _⟩ := gen_con h2 rfl
      rw [h0] at hD'; cases hD'; rw [h1] at hC'; cases hC'
      have ht := (sub_eqtele hS h5).2 (fun k A hk => by
        rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h1 k A hk) hσ
      simp only [{SB}]
      refine EqTm0.con h0 h1 {ST('h2')} {ST('h3')} ((sub_eqtele hS h4).2 {PARAMS} hσ) ?_ (by simpa using h6) ?_
      · rw [toList_subst hps, ← List.map_reverse]; exact ht
      · intro k r r' hr hr'
        rw [List.getElem?_map] at hr hr'
        obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.1 hr
        obtain ⟨r0', hr0', rfl⟩ := Option.map_eq_some_iff.1 hr'
        exact I_eq_subst (h7 k r0 r0' hr0 hr0') _""",
'elim': f"""by
      obtain ⟨D', hD', hps, hlen, hbs⟩ := gen_elim h1 rfl
      rw [h0] at hD'; cases hD'
      obtain ⟨_, _, _, _, hbs'⟩ := gen_elim h2 rfl
      simp only [{SB}]
      refine EqTm0.elim h0 {ST('h1')} {ST('h2')} ((sub_eqtele hS h3).2 {PARAMS} hσ)
        {E('h4',UPC('h4','eq'))} (by rw [toList_subst hbs, toList_subst hbs', List.length_map, List.length_map, h5]) ?_ {E('h7')}
      intro c C b b' hc hb hb'
      rw [toList_subst hbs, List.getElem?_map] at hb
      rw [toList_subst hbs', List.getElem?_map] at hb'
      obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
      obtain ⟨b0', hb0', rfl⟩ := Option.map_eq_some_iff.1 hb'
      have := (sub_eq hS (h6 c C b0 b0' hc hb0 hb0')).2 hσ
      rwa [branchTy_subst _ _ hS h0 hc hps hlen] at this""",
'conBnd': f"""by
      obtain ⟨D', C', hD', hC', _, hlen, hlena, hlenr⟩ := gen_con h6 rfl
      rw [h0] at hD'; cases hD'; rw [h1] at hC'; cases hC'
      have hb := hS.bnd _ _ _ _ _ _ _ h0 h1 h2
      rw [bndAt_subst _ _ (by rw [hlen, hlena, hlenr]; exact hb.2), ← toList_subst h4, ← toList_subst h5]
      exact EqTm0.conBnd h0 h1 h2 (by
          have := ent_trans hσ.ent (ent_subst h3 τ); rwa [cofAt_subst _ (by rw [hlenr]; exact hb.1)] at this)
        (isList_subst h4 _ _) (isList_subst h5 _ _) {T('h6')}""",
'elimCon': f"""by
      rw [elimCon_subst h3]; simp only [{SB}]
      refine EqTm0.elimCon h0 h1 ?_ (isList_subst h3 _ _) (isList_subst h4 _ _) {ST('h5')}
      rw [toList_subst h4, List.getElem?_map, h2]; rfl""",
'elimHcomp': f"by rw [elimHcomp_subst]; simp only [{SB}]; exact EqTm0.elimHcomp h0 {ST('h1')}",
'transpData0': f"by simp only [{SB}]; exact EqTm0.transpData0 h0 h1 {ST('h2')}",
'transpCon': f"""by
      obtain ⟨D', hD', hlen⟩ := gen_transp_data h5 rfl
      rw [h0] at hD'; cases hD'
      rw [transpCon_subst hS h0 h2 h3 h4 hlen]; simp only [{SB}]
      exact EqTm0.transpCon h0 h1 h2 (isList_subst h3 _ _) (isList_subst h4 _ _) {ST('h5')}""",
'transpHcomp': f"by rw [transpHcomp_subst]; simp only [{SB}]; exact EqTm0.transpHcomp h0 h1 {ST('h2')}",
}

fn={'HasTy0':'sub_ty','EqTm0':'sub_eq','HasTele0':'sub_tele','EqTele0':'sub_eqtele','Wf0':'sub_wf'}
def ctx(r):
    if r['name']=='restrict':
        return f"CtxSub.restrictSrc h1 ({fn[r['ind']]} hS h2).1"
    for i,p in enumerate(r['prem']):
        for k in ['HasTy0','EqTm0','Wf0','HasTele0','EqTele0']:
            if p.startswith(k+' S Ψ Φ Γ ') or p == k+' S Ψ Φ Γ':
                return f"sub_wf hS h{i}" if k=='Wf0' else f"({fn[k]} hS h{i}).1"
    raise Exception(r['name'])
def concl_args(c):
    # "HasTy0 S Ψ Φ Γ X Y" -> list of args after the head
    toks=[]; depth=0; cur=''
    for ch in c:
        if ch in '([': depth+=1
        if ch in ')]': depth-=1
        if ch==' ' and depth==0:
            if cur: toks.append(cur); cur=''
        else: cur+=ch
    if cur: toks.append(cur)
    return toks
out=[]
rs=parse()
out.append("""theorem sub_wf (hS : SigClosed S) {Ψ Φ Γ} : Wf0 S Ψ Φ Γ → CtxSub S Ψ Φ Γ
  | .nil _ => trivial
  | .cons h0 => ⟨(sub_ty hS h0).1, _, (sub_ty hS h0).2.1, (sub_ty hS h0).2.2,
      face_lemma (scoped_of_ty h0) (sub_ty hS h0).1 (sub_ty hS h0).2.1 (sub_ty hS h0).2.2 (Or.inl ⟨_, rfl⟩)⟩
""")
out.append("theorem sub_ty (hS : SigClosed S) {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A →\n    CtxSub S Ψ Φ Γ ∧ SubP S Ψ Φ Γ t A ∧ FunP S Ψ Φ Γ t A")
for r in rs:
    if r['ind']!='HasTy0': continue
    n=len(r['prem']); hs=" ".join(f"h{i}" for i in range(n))
    a=concl_args(r['concl'])
    pat=f"@HasTy0.{r['name']} _ {' '.join(r['binders'])} {hs}"
    out.append(f"  | {pat} =>\n    have hsub : SubP S {a[2]} {a[3]} {a[4]} {a[5]} {a[6]} := fun {{Ψ' Φ' Δ σ τ}} hσ =>\n      {sub['HasTy0'][r['name']]}\n    ⟨{ctx(r)}, hsub, fun {{Ψ' Φ' Δ σ1 τ1 σ2 τ2}} k1 k2 kE =>\n      {fun['HasTy0'][r['name']]}⟩")
out.append("")
out.append("""theorem sub_tele (hS : SigClosed S) {Ψ Φ Γ ts Δt prev} : HasTele0 S Ψ Φ Γ ts Δt prev →
    CtxSub S Ψ Φ Γ ∧ ((∀ (k : Nat) (A : Tm), Δt[k]? = some A → A.closedB (prev.length + k) 0 = true) →
      (∀ {Ψ' Φ' Δ σ τ}, TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ →
        HasTele0 S Ψ' Φ' Δ (ts.subst σ τ) Δt (prev.map (·.subst σ τ))) ∧
      (∀ {Ψ' Φ' Δ σ1 τ1 σ2 τ2}, TySub S Ψ Φ Γ Ψ' Φ' Δ σ1 τ1 → TySub S Ψ Φ Γ Ψ' Φ' Δ σ2 τ2 →
        EqSub S Ψ Γ Ψ' Φ' Δ σ1 τ1 σ2 τ2 →
        EqTele0 S Ψ' Φ' Δ (ts.subst σ1 τ1) (ts.subst σ2 τ2) Δt (prev.map (·.subst σ1 τ1))))""")
for r in rs:
    if r['ind']!='HasTele0': continue
    n=len(r['prem']); hs=" ".join(f"h{i}" for i in range(n))
    out.append(f"  | .{r['name']} {hs} => ⟨{ctx(r)}, fun hcl =>\n      {tele_sub[r['name']]}⟩")
out.append("")
out.append("""theorem sub_eqtele (hS : SigClosed S) {Ψ Φ Γ ts ts' Δt prev} : EqTele0 S Ψ Φ Γ ts ts' Δt prev →
    CtxSub S Ψ Φ Γ ∧ ((∀ (k : Nat) (A : Tm), Δt[k]? = some A → A.closedB (prev.length + k) 0 = true) →
      ∀ {Ψ' Φ' Δ σ τ}, TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ →
        EqTele0 S Ψ' Φ' Δ (ts.subst σ τ) (ts'.subst σ τ) Δt (prev.map (·.subst σ τ)))""")
for r in rs:
    if r['ind']!='EqTele0': continue
    n=len(r['prem']); hs=" ".join(f"h{i}" for i in range(n))
    out.append(f"  | .{r['name']} {hs} => ⟨{ctx(r)}, fun hcl =>\n      {eqtele_sub[r['name']]}⟩")
out.append("")
out.append("theorem sub_eq (hS : SigClosed S) {Ψ Φ Γ t u A} : EqTm0 S Ψ Φ Γ t u A → CtxSub S Ψ Φ Γ ∧\n    ∀ {Ψ' Φ' Δ σ τ}, TySub S Ψ Φ Γ Ψ' Φ' Δ σ τ →\n      EqTm0 S Ψ' Φ' Δ (t.subst σ τ) (u.subst σ τ) (A.subst σ τ)")
for r in rs:
    if r['ind']!='EqTm0': continue
    n=len(r['prem']); hs=" ".join(f"h{i}" for i in range(n))
    pat=f"@EqTm0.{r['name']} _ {' '.join(r['binders'])} {hs}"
    out.append(f"  | {pat} => ⟨{ctx(r)}, fun {{Ψ' Φ' Δ σ τ}} hσ =>\n    {eq[r['name']]}⟩")
out.append("")
hdr='''import KubusCore.Meta.SubBranch

/-!
# Metatheory: substitution is admissible

`sub_ty`/`sub_eq`: the minimal judgments are closed under simultaneous substitution of term
variables and interval variables (`TySub`), and typing is functional in the substitution
(`FunP`: judgmentally equal term substitutions and interval substitutions that are equal in
the free De Morgan algebra give judgmentally equal results). The two are proven together, and
the face rule's case uses `face_lemma`. The signature must be closed (`SigClosed`).
-/

set_option maxHeartbeats 4000000

namespace KubusCore.Meta

open Tm

variable {S : Sig}

mutual

'''
open('/home/agent/code/kubus-meta/KubusCore/Meta/Substitution.lean','w').write(hdr+"\n".join(out)+"end\n\nend KubusCore.Meta\n")
