import Model.Canon.KanBasic
open KubusCore KubusCore.Meta
theorem transpPi_body_inst (B w w0 u0 v : Tm) (φ : I) :
    (Tm.transp (B.subst (consT w wkS) I.var) φ (.app u0.shift w0)).inst v =
      .transp (B.inst (w.inst v.dshift)) φ (.app u0 (w0.inst v)) := by
  simp only [Tm.inst, Tm.subst, I_subst_var, I_up_var, shift_subst, subst_subst]
  congr 1
  · refine subst_congr (fun n => ?_) (fun i => ?_) B
    · rcases n with _ | n
      · simp only [consT]; exact subst_congr (fun n => by rcases n with _ | n <;> rfl) (fun i => rfl) w
      · rfl
    · rfl
  · congr 1
    exact subst_id_of (fun n => rfl) (fun i => rfl) u0
