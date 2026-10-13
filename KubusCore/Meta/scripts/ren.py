import sys
sys.path.insert(0,'/home/agent/code/kubus-meta/KubusCore/Meta/scripts')
from rules import parse
RN = "Tm.subst, I.subst, inst_subst, dinst_subst, rn_dup, dupS_rS, Iup_rI, up_rS, rn_dshift, rn_shift, rn_Ishift, equiv_subst, lit_rn, rS_up_zero, rI_up_zero, List.map_nil"
def S(x): return f"(by simpa only [{RN}] using {x})"
def T(h, R="hR"): return f"((ren_ty hS {h}).2 {R})"
def E(h, R="hR"): return f"((ren_eq hS {h}).2 {R})"
def ST(h, R="hR"): return S(T(h,R)[1:-1])
def SE(h, R="hR"): return S(E(h,R)[1:-1])
WF = "(hR.wf.wf hR.hscoped)"
ENT = lambda h: f"(ent_trans hR.ent (ent_subst {h} _))"

bodies = {}
# ---------------- HasTy0
bodies['HasTy0'] = {
'var': f"by simp only [Tm.subst, rS]; exact HasTy0.var {WF} (hR.look _ _ h1)",
'conv': f"HasTy0.conv {T('h0')} {E('h1')}",
'restrict': "(ren_ty hS h2).2 (hR.restrict hR.hscoped (ent_refl _) (ent_trans hR.ent (ent_subst h1 _)))",
'const': f"by obtain ⟨_, hA⟩ := hS.defn _ _ _ h1; rw [closed_subst_id hA (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))]; exact HasTy0.const {WF} h1",
'univ': f"HasTy0.univ h0 {WF}",
'cumul': f"HasTy0.cumul h0 {T('h1')}",
'pi': f"by simp only [{RN}]; exact HasTy0.pi {T('h0')} {T('h1','(hR.up (ren_ty hS h1).1)')}",
'lam': f"by simp only [{RN}]; exact HasTy0.lam {ST('h0')} {T('h1','(hR.up (ren_ty hS h1).1)')}",
'app': f"by simp only [{RN}]; exact HasTy0.app {ST('h0')} {T('h1')}",
'sigma': f"by simp only [{RN}]; exact HasTy0.sigma {T('h0')} {T('h1','(hR.up (ren_ty hS h1).1)')}",
'pair': f"by simp only [{RN}]; exact HasTy0.pair {ST('h0')} {T('h1')} {ST('h2')}",
'fst': f"by simp only [{RN}]; exact HasTy0.fst {ST('h0')}",
'snd': f"by simp only [{RN}]; exact HasTy0.snd {ST('h0')}",
'path': f"by simp only [{RN}]; exact HasTy0.path {T('h0','hR.dup')} {ST('h1')} {ST('h2')}",
'plam': f"by simp only [{RN}]; exact HasTy0.plam {ST('h0')} {T('h1','hR.dup')} {SE('h2')} {SE('h3')}",
'papp': f"by simp only [{RN}]; exact HasTy0.papp {ST('h0')} (hR.sc h1)",
'ipi': f"by simp only [{RN}]; exact HasTy0.ipi {WF} {T('h1','hR.dup')}",
'ilam': f"by simp only [{RN}]; exact HasTy0.ilam {ST('h0')} {T('h1','hR.dup')}",
'iapp': f"by simp only [{RN}]; exact HasTy0.iapp {ST('h0')} (hR.sc h1)",
'split': f"by simp only [{RN}]; exact HasTy0.split (hR.sc h0) (hR.sc h1) {S(ENT('h2'))} {T('h3')} {T('h4','(hR.underCof h0)')} {T('h5','(hR.underCof h1)')} {E('h6','((hR.underCof h0).underCof h1)')}",
'abort': f"HasTy0.abort {ENT('h0')} {T('h1')}",
'transp': f"by simp only [{RN}]; exact HasTy0.transp {T('h0','hR.dup')} (hR.sc h1) {SE('h2','(hR.underCof h1).dup')} {ST('h3')}",
'hcomp': f"by simp only [{RN}]; exact HasTy0.hcomp {T('h0')} (hR.sc h1) {ST('h2','(hR.underCof h1).dup')} {T('h3')} {SE('h4','(hR.underCof h1)')}",
'glue': f"by simp only [{RN}]; exact HasTy0.glue {T('h0')} (hR.sc h1) {T('h2','(hR.underCof h1)')} {ST('h3','(hR.underCof h1)')}",
'glueEl': f"by have hφ := scoped_cof_right (scoped_of_ty h1); simp only [{RN}]; exact HasTy0.glueEl {ST('h0')} {ST('h1','(hR.underCof hφ)')} {T('h2','(hR.underCof hφ)')} {T('h3')} {SE('h4','(hR.underCof hφ)')}",
'unglue': f"by have hφ := scoped_cof_right (scoped_of_ty h2); simp only [{RN}]; exact HasTy0.unglue {ST('h0')} {T('h1')} {ST('h2','(hR.underCof hφ)')} {ST('h3')}",
'data': f"by simp only [{RN}]; exact HasTy0.data h0 h1 ((ren_tele hS h2).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR)",
'con': f"""by
      have hlen := tele_length h4
      have ht := (ren_tele hS h5).2 (fun k A hk => by
        rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h1 k A hk) hR
      simp only [{RN}]
      refine HasTy0.con h0 h1 (isList_subst h2 _ _) {T('h3')}
        ((ren_tele hS h4).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR) ?_ (by simpa using h6) (fun r hr => ?_)
      · rw [toList_subst h2, ← List.map_reverse]; exact ht
      · obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr; exact hR.sc (h7 r0 hr0)""",
'elim': f"""by
      have hlen := tele_length h3
      simp only [{RN}]
      refine HasTy0.elim h0 (isList_subst h1 _ _) {T('h2')}
        ((ren_tele hS h3).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR)
        {T('h4','(hR.up (ren_ty hS h4).1)')} (isList_subst h5 _ _)
        (by rw [toList_subst h5, List.length_map, h6]) ?_ ?_ {T('h9')}
      · intro c C b hc hb
        rw [toList_subst h5, List.getElem?_map] at hb
        obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
        have := (ren_ty hS (h7 c C b0 hc hb0)).2 hR
        rwa [branchTy_subst _ _ hS h0 hc h1 hlen, up_rS] at this
      · intro c C b k ψ e hc hb hk
        rw [toList_subst h5, List.getElem?_map] at hb
        obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
        have hψ := hS.bnd _ _ _ _ _ _ _ h0 hc hk
        have := (ren_eq hS (h8 c C b0 k ψ e hc hb0 hk)).2
          (hR.branch hS h0 hc h1 hlen hψ.1 (ren_eq hS (h8 c C b0 k ψ e hc hb0 hk)).1)
        rw [rn_lift C.dims, ← IupN_rI, branchApp_subst, bndElim_subst _ _ h1 hlen h5 e hψ.2,
          branchBody_subst, up_rS] at this
        exact this""",

}
bodies['HasTele0'] = {
'nil': f"fun _ => fun hR => HasTele0.nil {WF}",
'cons': """fun hcl => fun hR => by
      have hA := hcl 0 _ List.getElem?_cons_zero
      rw [Nat.add_zero] at hA
      have := (ren_ty hS h0).2 hR
      rw [substList_subst hA] at this
      exact HasTele0.cons this ((ren_tele hS h1).2 (fun k B hk => by
        have := hcl (k + 1) B hk; simpa [Nat.add_assoc, Nat.add_comm 1] using this) hR)""",
}
bodies['EqTele0'] = {
'nil': f"fun _ => fun hR => EqTele0.nil {WF}",
'cons': """fun hcl => fun hR => by
      have hA := hcl 0 _ List.getElem?_cons_zero
      rw [Nat.add_zero] at hA
      have := (ren_eq hS h0).2 hR
      rw [substList_subst hA] at this
      exact EqTele0.cons this ((ren_eqtele hS h1).2 (fun k B hk => by
        have := hcl (k + 1) B hk; simpa [Nat.add_assoc, Nat.add_comm 1] using this) hR)""",
'dataInj': f"fun _ => fun hR => by simp only [{RN}]; exact EqTele0.dataInj h0 ((ren_tele hS h1).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR) ((ren_tele hS h2).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR) {SE('h3')}",
}
def kan(name, extra=""):
    return f"by rw [{name}_subst]; simp only [{RN}]; exact EqTm0.{name} {ST('h0')}{extra}"
bodies['EqTm0'] = {
'refl': f"EqTm0.refl {T('h0')}",
'symm': f"EqTm0.symm {E('h0')}",
'trans': f"EqTm0.trans {E('h0')} {E('h1')}",
'conv': f"EqTm0.conv {E('h0')} {E('h1')}",
'restrict': "(ren_eq hS h2).2 (hR.restrict hR.hscoped (ent_refl _) (ent_trans hR.ent (ent_subst h1 _)))",
'cumul': f"EqTm0.cumul h0 {E('h1')}",
'delta': f"""by
      obtain ⟨ht, hA⟩ := hS.defn _ _ _ h1
      have h00 : ∀ x, x < 0 → x < 0 := fun _ h => h
      rw [closed_subst_id hA (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _)),
        closed_subst_id ht (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))]
      have := {T('h0')}
      rw [closed_subst_id hA (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))] at this
      exact EqTm0.delta this h1""",
'absurd': f"EqTm0.absurd {ENT('h0')} {T('h1')} {T('h2')}",
'local': f"by exact EqTm0.local (hR.sc h0) (hR.sc h1) {S(ENT('h2'))} {T('h3')} {T('h4')} {E('h5','(hR.underCof h0)')} {E('h6','(hR.underCof h1)')}",
'face': f"by rw [dset_rn hR.inj]; exact EqTm0.face (hR.bound _ h0) {S(ENT('h1'))} {T('h2')} {T('h3')}",
'faceU': f"by rw [dset_rn hR.inj]; exact EqTm0.faceU (hR.bound _ h0) {S(ENT('h1'))} {T('h2')}",
'pi': f"by simp only [{RN}]; exact EqTm0.pi {E('h0')} {E('h1','(hR.up (ren_eq hS h1).1)')}",
'lam': f"by simp only [{RN}]; exact EqTm0.lam {ST('h0')} {E('h1','(hR.up (ren_eq hS h1).1)')}",
'app': f"by simp only [{RN}]; exact EqTm0.app {SE('h0')} {E('h1')}",
'sigma': f"by simp only [{RN}]; exact EqTm0.sigma {E('h0')} {E('h1','(hR.up (ren_eq hS h1).1)')}",
'pair': f"by simp only [{RN}]; exact EqTm0.pair {ST('h0')} {E('h1')} {SE('h2')}",
'fst': f"by simp only [{RN}]; exact EqTm0.fst {SE('h0')}",
'snd': f"by simp only [{RN}]; exact EqTm0.snd {SE('h0')}",
'path': f"by simp only [{RN}]; exact EqTm0.path {E('h0','hR.dup')} {SE('h1')} {SE('h2')}",
'plam': f"by simp only [{RN}]; exact EqTm0.plam {ST('h0')} {ST('h1')} {ST('h2')} {E('h3','hR.dup')}",
'papp': f"by simp only [{RN}]; exact EqTm0.papp {SE('h0')} (hR.sc h1) (hR.sc h2) (I_eq_subst h3 _)",
'split': f"by have hφ := scoped_cof_right (scoped_of_eq h2); have hψ := scoped_cof_right (scoped_of_eq h3); simp only [{RN}]; exact EqTm0.split {ST('h0')} {ST('h1')} {E('h2','(hR.underCof hφ)')} {E('h3','(hR.underCof hψ)')}",
'transp': f"by simp only [{RN}]; exact EqTm0.transp {ST('h0')} {ST('h1')} {E('h2','hR.dup')} (ent_subst h3 _) (ent_subst h4 _) {SE('h5')}",
'hcomp': f"by have hφ := scoped_cof_shift_right (scoped_of_eq h5); simp only [{RN}]; exact EqTm0.hcomp {ST('h0')} {ST('h1')} {E('h2')} (ent_subst h3 _) (ent_subst h4 _) {SE('h5','(hR.underCof hφ).dup')} {E('h6')}",
'glue': f"by have hφ := scoped_cof_right (scoped_of_eq h5); simp only [{RN}]; exact EqTm0.glue {ST('h0')} {ST('h1')} {E('h2')} (ent_subst h3 _) (ent_subst h4 _) {E('h5','(hR.underCof hφ)')} {SE('h6','(hR.underCof hφ)')}",
'glueEl': f"by have hφ := scoped_cof_right (scoped_of_eq h4); simp only [{RN}]; exact EqTm0.glueEl {ST('h0')} {ST('h1')} (ent_subst h2 _) (ent_subst h3 _) {SE('h4','(hR.underCof hφ)')} {E('h5','(hR.underCof hφ)')} {E('h6')}",
'unglue': f"by have hφ := scoped_cof_right (scoped_of_eq h4); simp only [{RN}]; exact EqTm0.unglue {ST('h0')} {ST('h1')} (ent_subst h2 _) (ent_subst h3 _) {SE('h4','(hR.underCof hφ)')} {SE('h5')}",
'ipi': f"by simp only [{RN}]; exact EqTm0.ipi {WF} {E('h1','hR.dup')}",
'ilam': f"by simp only [{RN}]; exact EqTm0.ilam {ST('h0')} {E('h1','hR.dup')}",
'iapp': f"by simp only [{RN}]; exact EqTm0.iapp {SE('h0')} (hR.sc h1) (hR.sc h2) (I_eq_subst h3 _)",
'noConf': f"EqTm0.noConf (headClash_subst _ _ h0) {E('h1')} {T('h2')} {T('h3')}",
'piInjDom': f"by simp only [{RN}]; exact EqTm0.piInjDom {SE('h0')}",
'piInjCod': f"by simp only [{RN}]; exact EqTm0.piInjCod {SE('h0')} {T('h1')}",
'sigmaInjDom': f"by simp only [{RN}]; exact EqTm0.sigmaInjDom {SE('h0')}",
'sigmaInjCod': f"by simp only [{RN}]; exact EqTm0.sigmaInjCod {SE('h0')} {T('h1')}",
'pathInjLine': f"by simp only [{RN}]; exact EqTm0.pathInjLine {SE('h0')} (hR.sc h1)",
'pathInjLeft': f"by simp only [{RN}]; exact EqTm0.pathInjLeft {SE('h0')}",
'pathInjRight': f"by simp only [{RN}]; exact EqTm0.pathInjRight {SE('h0')}",
'ipiInj': f"by simp only [{RN}]; exact EqTm0.ipiInj {SE('h0')} (hR.sc h1)",
'piBeta': f"by simp only [{RN}]; exact EqTm0.piBeta {ST('h0')}",
'piEta': f"by simp only [{RN}]; exact EqTm0.piEta {ST('h0')}",
'fstBeta': f"by simp only [{RN}]; exact EqTm0.fstBeta {ST('h0')}",
'sndBeta': f"by simp only [{RN}]; exact EqTm0.sndBeta {ST('h0')}",
'sigmaEta': f"by simp only [{RN}]; exact EqTm0.sigmaEta {ST('h0')}",
'pathBeta': f"by simp only [{RN}]; exact EqTm0.pathBeta {ST('h0')}",
'pathEta': f"by simp only [{RN}]; exact EqTm0.pathEta {ST('h0')}",
'ipiEta': f"by simp only [{RN}]; exact EqTm0.ipiEta {ST('h0')}",
'pathZero': f"by simp only [{RN}]; exact EqTm0.pathZero {ST('h0')}",
'pathOne': f"by simp only [{RN}]; exact EqTm0.pathOne {ST('h0')}",
'splitL': f"by simp only [{RN}]; exact EqTm0.splitL {ENT('h0')} {ST('h1')}",
'splitR': f"by simp only [{RN}]; exact EqTm0.splitR {ENT('h0')} {ST('h1')}",
'transpFace': f"by simp only [{RN}]; exact EqTm0.transpFace {ENT('h0')} {ST('h1')}",
'hcompFace': f"by simp only [{RN}]; exact EqTm0.hcompFace {ENT('h0')} {ST('h1')}",
'transpU': f"by simp only [{RN}]; exact EqTm0.transpU {ST('h0')}",
'transpPi': kan('transpPi'), 'transpSigma': kan('transpSigma'), 'transpPath': kan('transpPath'),
'transpIPi': kan('transpIPi'), 'hcompIPi': kan('hcompIPi'), 'hcompPi': kan('hcompPi'),
'hcompSigma': kan('hcompSigma'), 'hcompPath': kan('hcompPath'), 'hcompU': kan('hcompU'),
'hcompGlue': f"by have hφ := scoped_cof_right (scoped_of_ty h2); rw [hcompGlue_subst]; simp only [{RN}]; exact EqTm0.hcompGlue {ST('h0')} {T('h1')} {ST('h2','(hR.underCof hφ)')}",
'transpGlue': f"""by
      have hφ := scoped_cof_right (scoped_of_ty h2)
      rw [transpGlueWith_subst]; simp only [{RN}]
      exact EqTm0.transpGlue {ST('h0')} {T('h1','hR.dup')} {ST('h2','(hR.dup.underCof hφ)')} (hR.sc h3)
        (ent_trans (ent_subst h4 _) (by simpa only [Iup_rI] using (forall0_subst _ (rI δ)).1))
        (ent_trans (by simpa only [Iup_rI] using (forall0_subst _ (rI δ)).2) (ent_subst h5 _))""",
'glueFace': f"by simp only [{RN}]; exact EqTm0.glueFace {ENT('h0')} {ST('h1')}",
'glueElFace': f"by simp only [{RN}]; exact EqTm0.glueElFace {ENT('h0')} {ST('h1')}",
'unglueFace': f"by simp only [{RN}]; exact EqTm0.unglueFace {ENT('h0')} {ST('h1')} {T('h2')} {ST('h3')}",
'glueBeta': f"by simp only [{RN}]; exact EqTm0.glueBeta {ST('h0')} {ST('h1')}",
'glueEta': f"by simp only [{RN}]; exact EqTm0.glueEta {ST('h0')}",
'data': f"by simp only [{RN}]; exact EqTm0.data h0 {T('h1')} {T('h2')} ((ren_eqtele hS h3).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR)",
'con': f"""by
      obtain ⟨D', C', hD', hC', hps, hlen, _, _⟩ := gen_con h2 rfl
      rw [h0] at hD'; cases hD'; rw [h1] at hC'; cases hC'
      have ht := (ren_eqtele hS h5).2 (fun k A hk => by
        rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h1 k A hk) hR
      simp only [{RN}]
      refine EqTm0.con h0 h1 {ST('h2')} {ST('h3')} ((ren_eqtele hS h4).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR) ?_ (by simpa using h6) ?_
      · rw [toList_subst hps, ← List.map_reverse]; exact ht
      · intro k r r' hr hr'
        rw [List.getElem?_map] at hr hr'
        obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.1 hr
        obtain ⟨r0', hr0', rfl⟩ := Option.map_eq_some_iff.1 hr'
        exact I_eq_subst (h7 k r0 r0' hr0 hr0') _""",
'elim': f"""by
      obtain ⟨D', hD', hps, hlen, _⟩ := gen_elim h1 rfl
      rw [h0] at hD'; cases hD'
      simp only [{RN}]
      refine EqTm0.elim h0 {ST('h1')} {ST('h2')} ((ren_eqtele hS h3).2 (fun k A hk => by simpa using hS.params _ _ _ _ h0 hk) hR)
        {E('h4','(hR.up (ren_eq hS h4).1)')} (isList_subst h5 _ _) (isList_subst h6 _ _)
        (by rw [toList_subst h5, toList_subst h6, List.length_map, List.length_map, h7]) ?_ {E('h9')}
      intro c C b b' hc hb hb'
      rw [toList_subst h5, List.getElem?_map] at hb
      rw [toList_subst h6, List.getElem?_map] at hb'
      obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
      obtain ⟨b0', hb0', rfl⟩ := Option.map_eq_some_iff.1 hb'
      have := (ren_eq hS (h8 c C b0 b0' hc hb0 hb0')).2 hR
      rwa [branchTy_subst _ _ hS h0 hc hps hlen, up_rS] at this""",
'conBnd': f"""by
      obtain ⟨D', C', hD', hC', _, hlen, hlena, hlenr⟩ := gen_con h6 rfl
      rw [h0] at hD'; cases hD'; rw [h1] at hC'; cases hC'
      have hb := hS.bnd _ _ _ _ _ _ _ h0 h1 h2
      rw [bndAt_subst _ _ (by rw [hlen, hlena, hlenr]; exact hb.2), ← toList_subst h4, ← toList_subst h5]
      exact EqTm0.conBnd h0 h1 h2 (by
          have := ent_trans hR.ent (ent_subst h3 (rI δ)); rwa [cofAt_subst _ (by rw [hlenr]; exact hb.1)] at this)
        (isList_subst h4 _ _) (isList_subst h5 _ _) {T('h6')}""",
'elimCon': f"""by
      obtain ⟨D', hD', _, hlen, _⟩ := gen_elim h7 rfl
      rw [h0] at hD'; cases hD'
      have ht := (ren_tele hS h6).2 (fun k A hk => by rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h1 k A hk) hR
      rw [elimCon_subst h4]; simp only [{RN}]
      refine EqTm0.elimCon h0 h1 ?_ (isList_subst h3 _ _) (isList_subst h4 _ _) (isList_subst h5 _ _) ?_ {ST('h7')}
      · rw [toList_subst h5, List.getElem?_map, h2]; rfl
      · rw [toList_subst h3, ← List.map_reverse]; exact ht""",
'elimHcomp': f"by rw [elimHcomp_subst]; simp only [{RN}]; exact EqTm0.elimHcomp h0 {ST('h1')} {ST('h2')}",
'transpData0': f"by simp only [{RN}]; exact EqTm0.transpData0 h0 h1 {ST('h2')}",
'transpCon': f"""by
      obtain ⟨D', hD', hlen0⟩ := gen_transp_data h6 rfl
      rw [h0] at hD'; cases hD'
      have hlen := hlen0
      rw [← List.length_map (f := (·.dinst .zero)), ← dinst_toList h3] at hlen
      have ht := (ren_tele hS h5).2 (fun k A hk => by rw [List.length_reverse, hlen]; exact argTys_closed hS h0 h2 k A hk) hR
      rw [transpCon_subst hS h0 h2 h3 h4 hlen0]; simp only [{RN}]
      refine EqTm0.transpCon h0 h1 h2 (isList_subst h3 _ _) (isList_subst h4 _ _) ?_ {ST('h6')}
      rw [dinst_toList (isList_subst h3 _ _), toList_subst h3]
      rw [dinst_toList h3] at ht
      simpa only [List.map_reverse, List.map_map, Function.comp_def, dinst_subst, I.subst, {RN}] using ht""",
'transpHcomp': f"by rw [transpHcomp_subst]; simp only [{RN}]; exact EqTm0.transpHcomp h0 h1 {ST('h2')} {ST('h3')}",
}

fn={'HasTy0':'ren_ty','EqTm0':'ren_eq','HasTele0':'ren_tele','EqTele0':'ren_eqtele','Wf0':'ren_wf'}
def ctx(r):
    if r['name']=='restrict':
        return f"CtxRen.restrict h1 ({fn[r['ind']]} hS h2).1"
    for i,p in enumerate(r['prem']):
        for k in ['HasTy0','EqTm0','Wf0','HasTele0','EqTele0']:
            if p.startswith(k+' S Ψ Φ Γ ') or p == k+' S Ψ Φ Γ':
                return f"ren_wf hS h{i}" if k=='Wf0' else f"({fn[k]} hS h{i}).1"
    raise Exception(r['name'])
out=[]
rs=parse()
sigs = {
'HasTy0': "theorem ren_ty (hS : SigClosed S) {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → CtxRen S Ψ Φ Γ ∧\n    ∀ {Ψ' Φ' Δ ρ δ}, TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ →\n      HasTy0 S Ψ' Φ' Δ (t.subst (rS ρ) (rI δ)) (A.subst (rS ρ) (rI δ))",
'HasTele0': "theorem ren_tele (hS : SigClosed S) {Ψ Φ Γ ts Δt prev} : HasTele0 S Ψ Φ Γ ts Δt prev →\n    CtxRen S Ψ Φ Γ ∧ ((∀ (k : Nat) (A : Tm), Δt[k]? = some A → A.closedB (prev.length + k) 0 = true) →\n    ∀ {Ψ' Φ' Δ ρ δ}, TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ →\n      HasTele0 S Ψ' Φ' Δ (ts.subst (rS ρ) (rI δ)) Δt (prev.map (·.subst (rS ρ) (rI δ))))",
'EqTele0': "theorem ren_eqtele (hS : SigClosed S) {Ψ Φ Γ ts ts' Δt prev} : EqTele0 S Ψ Φ Γ ts ts' Δt prev →\n    CtxRen S Ψ Φ Γ ∧ ((∀ (k : Nat) (A : Tm), Δt[k]? = some A → A.closedB (prev.length + k) 0 = true) →\n    ∀ {Ψ' Φ' Δ ρ δ}, TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ →\n      EqTele0 S Ψ' Φ' Δ (ts.subst (rS ρ) (rI δ)) (ts'.subst (rS ρ) (rI δ)) Δt (prev.map (·.subst (rS ρ) (rI δ))))",
'EqTm0': "theorem ren_eq (hS : SigClosed S) {Ψ Φ Γ t u A} : EqTm0 S Ψ Φ Γ t u A → CtxRen S Ψ Φ Γ ∧\n    ∀ {Ψ' Φ' Δ ρ δ}, TyRen S Ψ Φ Γ Ψ' Φ' Δ ρ δ →\n      EqTm0 S Ψ' Φ' Δ (t.subst (rS ρ) (rI δ)) (u.subst (rS ρ) (rI δ)) (A.subst (rS ρ) (rI δ))",
}
out.append("""theorem ren_wf (hS : SigClosed S) {Ψ Φ Γ} : Wf0 S Ψ Φ Γ → CtxRen S Ψ Φ Γ
  | .nil _ => trivial
  | .cons h0 => ⟨(ren_ty hS h0).1, fun _ _ _ _ _ hR => ⟨_, (ren_ty hS h0).2 hR⟩⟩
""")
for ind in ['HasTy0','HasTele0','EqTele0','EqTm0']:
    out.append(sigs[ind])
    for r in rs:
        if r['ind']!=ind: continue
        n=len(r['prem'])
        hs=" ".join(f"h{i}" for i in range(n))
        b=bodies[ind].get(r['name'],'sorry')
        if ind in ('HasTele0','EqTele0'):
            out.append(f"  | .{r['name']} {hs} => ⟨{ctx(r)},\n    {b}⟩")
        else:
            out.append(f"  | .{r['name']} {hs} => ⟨{ctx(r)}, fun {{Ψ' Φ' Δ ρ δ}} hR =>\n    {b}⟩")
    out.append("")
body="\n".join(out)
hdr='''import KubusCore.Meta.RenLemmas

/-!
# Metatheory: renaming is admissible

`ren_ty`/`ren_eq`: the minimal judgments are closed under renaming term variables arbitrarily
and interval variables injectively (`TyRen`), in particular under weakening by a term variable
(`HasTy.wk`) or an interval variable (`HasTy.dwk`). The signature must be closed (`SigClosed`,
implied by `WfSig`). Every derivation also yields `CtxRen` for its context, which provides the
well-formedness of the renamed context under binders.
-/

set_option maxHeartbeats 1000000

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem rS_up_zero (ρ : Nat → Nat) : rS (upRen ρ) 0 = .var 0 := rfl
theorem rI_up_zero (δ : Nat → Nat) : rI (upRen δ) 0 = .var 0 := rfl

theorem argTys_closed (hS : SigClosed S) {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor}
    (hd : S[d]? = some (.data D)) (hc : D.ctors[c]? = some C) (k : Nat) (A : Tm)
    (hk : (C.argTys d D.params.length)[k]? = some A) : A.closedB (D.params.length + k) 0 = true := by
  simp only [Ctor.argTys, List.getElem?_map] at hk
  obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.1 hk
  have : k' = k := by
    have := List.getElem?_eq_some_iff.1 hk'
    simp only [List.getElem_range] at this; exact this.2.symm
  subst this
  exact argTy_closed hS hd hc k'

theorem rn_lift (m : Nat) {k : Nat} {ρ : Nat → Nat} : rS (upRenN k ρ) = dupN m (upN k (rS ρ)) := by
  rw [upN_rS, dupN_rS]

mutual

'''
open('/home/agent/code/kubus-meta/KubusCore/Meta/Ren.lean','w').write(hdr+body+"end\n\nend KubusCore.Meta\n")
