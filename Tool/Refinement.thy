theory Refinement
  imports Hoare
begin

no_notation Fixpoint.pleq (infix "\<sqsubseteq>" 50)
notation Set.image (infixr "``" 90)

definition spec :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a predT" ("\<lbrakk>_, _\<rbrakk>" [10, 10] 100)  where
  "\<lbrakk>P, Q\<rbrakk> \<equiv> Sup {F. \<turnstile> P F Q \<and> mono F}"

lemma specE: "\<turnstile> P \<lbrakk>P, Q\<rbrakk> Q"
  apply (simp add: ht_def spec_def)
  apply (rule SUP_upper)
  by (auto simp: mono_def)

lemma specI: "mono F \<Longrightarrow> \<turnstile> P F Q \<Longrightarrow> F \<le> \<lbrakk>P, Q\<rbrakk>"
  apply (simp add: ht_def spec_def)
  apply (rule Sup_upper)
  by auto

abbreviation spec_ref :: "'a predT \<Rightarrow> 'a predT \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "F \<sqsubseteq> G \<equiv> G \<le> F"

(* Refinement rules *)

lemma ref_strenthen: "P \<le> P' \<Longrightarrow> \<lbrakk>P, Q\<rbrakk> \<sqsubseteq> \<lbrakk>P', Q\<rbrakk>"
  apply (simp add: spec_def)
  apply (rule Sup_mono)
  by (auto intro: hl_strenthen)

lemma ref_weaken: "Q' \<le> Q \<Longrightarrow> \<lbrakk>P, Q\<rbrakk> \<sqsubseteq> \<lbrakk>P, Q'\<rbrakk>"
  apply (simp add: spec_def)
  apply (rule Sup_mono)
  apply auto
  apply (rule_tac x=\<top> in exI)
  by (auto simp: ht_def mono_def)

lemma ref_str_weak: "P \<le> P' \<Longrightarrow> Q' \<le> Q \<Longrightarrow> \<lbrakk>P, Q\<rbrakk> \<sqsubseteq> \<lbrakk>P', Q'\<rbrakk>"
  by (metis dual_order.trans ref_strenthen ref_weaken)

lemma ref_seq: "\<lbrakk>P, Q\<rbrakk> \<sqsubseteq> \<lbrakk>P, R\<rbrakk>; \<lbrakk>R, Q\<rbrakk>"
  apply (simp add: spec_def)
  apply (rule Sup_upper)
  by (auto simp: ht_def mono_def)

lemma ref_assign: "P \<le> Q[` |m| /`v] \<Longrightarrow> \<lbrakk>P, Q\<rbrakk> \<sqsubseteq> (`v := ` |m| )"
  apply (drule hl_assign)
  apply (simp add: ht_def spec_def)
  apply (rule Sup_upper)
  by (auto simp: mono_def)

lemma ref_lassign: "P \<le> P'[` |m|/`v] \<Longrightarrow> \<lbrakk>P, Q\<rbrakk> \<sqsubseteq> (`v := ` |m| ); \<lbrakk>P', Q\<rbrakk>"
  apply (drule ref_assign)
  apply (subgoal_tac "\<lbrakk>P, Q \<rbrakk> \<sqsubseteq> \<lbrakk>P, P'\<rbrakk>; \<lbrakk>P', Q\<rbrakk>")
  apply simp
  apply (rule order_trans [of _ "\<lbrakk>P, P'\<rbrakk> \<circ> \<lbrakk>P', Q\<rbrakk>"])
  apply (rule PT.Sup.qisor)
  apply force
  apply force
  by (rule ref_seq)

lemma mono_spec: "mono (\<lbrakk>p, q\<rbrakk>)"
  by (auto simp: spec_def mono_def)

lemma mono_wi: "mono (\<Squnion>{F. p \<sqinter> b \<le> F p \<and> mono (F :: 'a predT)})"
  apply (subst mono_def)
  apply simp
  apply (rule allI)+
  apply (rule impI)
  apply (rule SUP_mono)
  apply (rule_tac x=f in bexI)
  apply (clarsimp simp: mono_def)
  apply simp
done

lemma ref_while_inv: "\<lbrakk>p, p - b\<rbrakk> \<sqsubseteq> while_comm b (\<lbrakk>p \<sqinter> b, p\<rbrakk>)"
  apply (rule specI)
  apply (unfold while_comm_def)
  apply (fold while_inv_comm_def[of b p "\<lbrakk>p \<sqinter> b, p\<rbrakk>"])
  apply (subst while_inv_comm_def)
  apply (rule mono_seq)
  apply (rule mono_iteration)
  apply (rule mono_seq)
  apply (rule mono_pred)
defer
  apply (rule mono_pred)
  apply (rule hl_while)
  apply (auto simp: spec_def)
  apply (unfold ht_def)
  defer
  apply (rule_tac x=skip in exI)
  apply (clarsimp intro!: mono_skip)
  apply (rule mono_wi)+
done

lemma isol: "G \<sqsubseteq> F \<Longrightarrow> mono H \<Longrightarrow> H \<circ> G \<sqsubseteq> H \<circ> F"
  apply (rule le_funI)
  apply (subst comp_apply)+
  by (metis le_funE monoD)

lemma isol2: "F \<sqsubseteq> G o H \<Longrightarrow> mono I \<Longrightarrow> (I o F) \<sqsubseteq> (I o G) o H"
  apply (subst comp_assoc)
  apply (rule isol)
  by auto

lemma ref_while: "i \<sqinter> \<lbrace>`b\<rbrace> \<le> p' \<Longrightarrow> p \<le> i \<Longrightarrow> i - \<lbrace>`b\<rbrace> \<le> q \<Longrightarrow> \<lbrakk>p, q\<rbrakk> \<sqsubseteq> while `b do \<lbrakk>p', i\<rbrakk> od"
proof -
  assume assms: "i \<sqinter> \<lbrace>`b\<rbrace> \<le> p'" "p \<le> i" "i - \<lbrace>`b\<rbrace> \<le> q"
  have a: "\<lbrakk>p, q\<rbrakk> \<sqsubseteq> \<lbrakk>i, i -\<lbrace>`b\<rbrace>\<rbrakk>"
    apply (rule ref_str_weak)
    using assms by auto
  also have b: "\<lbrakk>i, i -\<lbrace>`b\<rbrace>\<rbrakk> \<sqsubseteq> while `b do \<lbrakk> i \<sqinter> \<lbrace>`b\<rbrace>, i\<rbrakk> od"
    using ref_while_inv[of "\<lbrace>`b\<rbrace>" i]
    by auto
  have c: "while `b do \<lbrakk> i \<sqinter> \<lbrace>`b\<rbrace>, i\<rbrakk> od \<sqsubseteq> while `b do \<lbrakk>p', i\<rbrakk> od"
    apply (unfold while_comm_def)
    apply (rule PT.Sup.qisor)
    using assms
    by (smt2 antisym_conv ht_def mono_def order_refl specI top_apply top_greatest)
  show ?thesis
    by (metis (no_types, lifting) b c calculation dual_order.trans)
qed   

lemma star_unfoldl: "mono x \<Longrightarrow> id \<squnion> x o x\<^sup>\<star> \<le> x\<^sup>\<star>"
  oops

lemma mono_qSup_subdistl: "mono (f :: 'a :: complete_lattice \<Rightarrow> 'a) \<Longrightarrow> \<Squnion>((\<lambda>g. f o g) `` G) \<le> f \<circ> \<Squnion>G"
  by (rule Sup_least) (auto intro!: le_funI order_class.monoD[of "\<lambda>x. f x"] SUP_upper)

lemma pow_iso: "F \<le> G \<Longrightarrow> pow F i \<le> pow G i"
  apply (induct i)
  apply auto
oops

lemma iteration_iso: "mono G \<Longrightarrow> F \<le> G \<Longrightarrow> F\<^sup>\<star> \<le> G\<^sup>\<star>"
  apply (simp add: iteration_def)
  apply (rule Inf_mono)
  apply auto
  apply (rule_tac x="pow F i" in exI)
  apply (rule conjI)
  apply force
  apply (induct_tac i)
  by (auto simp: mono_def pow_zero pow_suc)

lemma "F \<sqsubseteq> G \<Longrightarrow> F o R \<sqsubseteq> G o R"
  by auto

lemma while_iso: "mono F \<Longrightarrow> F \<sqsubseteq> G \<Longrightarrow> while_comm b F \<sqsubseteq> while_comm b G"
  apply (unfold while_comm_def)
  apply (rule Semantics.PT.Sup.qisor)
  apply (rule iteration_iso)
  apply (rule mono_seq)
  apply (rule mono_pred)
  apply auto
  done

lemma spec_ref_trans [trans]: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
  by auto

lemma spec_ref_trans2 [trans]: "y \<le> x \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
  by auto

lemma pred_infI: "p s \<and> q s \<Longrightarrow> (p \<sqinter> q) s"
  by auto


(* Refinement tactic *)
ML {*

val refinement_step_tac = 
  FIRST' [
    rtac @{thm mono_spec},
    rtac @{thm mono_seq},
    rtac @{thm mono_assign},
    rtac @{thm mono_mutation},
    rtac @{thm isol},
    rtac @{thm isol2},
    rtac @{thm while_iso}, 
    rtac @{thm ref_lassign},
    rtac @{thm ref_assign},
    rtac @{thm ref_seq},
    rtac @{thm ref_strenthen},
    rtac @{thm ref_weaken},
    rtac @{thm ref_str_weak},
    rtac @{thm ref_while}
  ]

val format_step_tac = FIRST' [
    rtac @{thm pred_infI},
    rtac @{thm conjI}
  ]

val format_tac = REPEAT_ALL_NEW (CHANGED o format_step_tac)

val refinement_tac = REPEAT_ALL_NEW (CHANGED o refinement_step_tac)

*}

method_setup refinement = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD (
    ALLGOALS refinement_tac
    THEN TRY (ALLGOALS (clarify_tac ctxt))
    THEN TRY (ALLGOALS (EqSubst.eqsubst_asm_tac ctxt [1] [@{thm "sep_conj_eq"}]))
    THEN TRY (ALLGOALS (EqSubst.eqsubst_asm_tac ctxt [1] [@{thm "sep_conj_eq"}]))
    THEN TRY (ALLGOALS format_tac)
    THEN TRY (ALLGOALS (clarify_tac ctxt))
  ))
*}



end
