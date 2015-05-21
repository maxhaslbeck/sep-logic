theory Hoare
  imports Semantics
begin

definition ht :: "'a pred \<Rightarrow> 'a predT \<Rightarrow> 'a pred \<Rightarrow> bool" ("(3\<turnstile> _/ (2_)/ _)" [100, 55, 100] 50) where
  "\<turnstile> p F q \<longleftrightarrow> p \<le> F q"

lemma hl_seq: "mono F \<Longrightarrow> \<turnstile> p F r \<Longrightarrow> \<turnstile> r G q \<Longrightarrow> \<turnstile> p F; G q"
  by (auto simp: ht_def mono_def)

lemma hl_sup: "mono F \<Longrightarrow> p \<le> (F :: 'a predT) q \<Longrightarrow> p \<le> F r \<Longrightarrow> p \<le> F (q \<squnion> r)"
  by (metis mono_sup order_trans sup_ge2)

lemma hl_skip: "p \<le> q \<Longrightarrow> \<turnstile> p skip q"
  by (auto simp: ht_def)

lemma hl_if: "\<turnstile> (p \<sqinter> b) F q \<Longrightarrow> \<turnstile> (p - b) G q \<Longrightarrow> \<turnstile> p (if_comm b F G) q"
  by (auto simp: ht_def if_comm_def)

lemma hl_weaken: "mono F \<Longrightarrow> q \<le> q' \<Longrightarrow> \<turnstile> p F q \<Longrightarrow> \<turnstile> p F q'"
  by (auto simp: ht_def mono_def)

lemma hl_strenthen: "p' \<le> p \<Longrightarrow> \<turnstile> p F q \<Longrightarrow> \<turnstile> p' F q"
  by (auto simp: ht_def)

lemma iteration: "p \<le> F q \<Longrightarrow> p \<le> (F\<^sup>\<star>) q"
  oops

lemma hl_pow: "mono F \<Longrightarrow> p \<le> F p \<Longrightarrow> pow F i p \<le> F (pow F i p)"
  apply (induct i)
  apply (auto simp: pow_zero pow_suc)
  by (metis mono_def predicate1D)

lemma hl_iteration: "mono F \<Longrightarrow> p \<le> F p \<Longrightarrow> p \<le> (F\<^sup>\<star>) p"
  apply (simp add: iteration_def)
  apply (rule INF_greatest)
  apply auto
  apply (induct_tac i)
  apply (auto simp: pow_zero pow_suc)
  by (metis hl_pow predicate1D)

lemma hl_while': "mono x \<Longrightarrow> (i \<sqinter> b) \<le> x i \<Longrightarrow> i \<le> ((\<lceil>b\<rceil> \<circ> x)\<^sup>\<star>) i"
  apply (rule hl_iteration)
  apply (auto simp: mono_def)
done

lemma mono_bx: "mono x \<Longrightarrow> mono ((\<lceil>b\<rceil> \<circ> x)\<^sup>\<star>)"
  apply (rule mono_iteration)
  apply (rule mono_seq)
  apply (rule mono_pred)
by simp

lemma hl_while: "mono x \<Longrightarrow> p \<le> i \<Longrightarrow> i - b \<le> q \<Longrightarrow> (i \<sqinter> b) \<le> x i \<Longrightarrow> \<turnstile> p (while_inv_comm b i x) q"
  apply (rule hl_weaken)
  apply (unfold while_inv_comm_def)
  apply (rule mono_seq)
  apply (rule mono_iteration)
  apply (rule mono_seq)
  apply (rule mono_pred)
  apply simp
  apply (rule mono_pred)  
  apply assumption
  apply (rule hl_strenthen)
  apply assumption
  apply (unfold ht_def while_inv_comm_def)
  apply (subst comp_apply)
  apply (rule order_trans)
  apply (rule hl_while')
  apply assumption
  apply assumption
  apply (rule monoE[of "(\<lceil>b\<rceil> \<circ> x)\<^sup>\<star>" i "\<lceil>- b\<rceil> (i - b)"])
  apply (rule mono_bx)
  apply (auto intro: mono_def)
done

lemma sl_frame: "local F \<Longrightarrow> \<turnstile> p F q \<Longrightarrow> \<turnstile> (p * r) F (q * r)"
proof (simp add: local_def ht_def)
  assume assm: "\<forall>x y. F x * y \<le> F (x * y)" "p \<le> F q"
  hence "p * r \<le> F q * r"
    by (metis Semantics.Sup.qisor)
  thus "p * r \<le> F (q * r)" using assm
    by auto
qed

lemma hl_assign: "P \<le> Q[` |m| /`x] \<Longrightarrow> \<turnstile> P (`x := ` |m| ) Q"
  by (auto simp: ht_def)

lemma sl_assign: "(\<And>s h. P (s, h) \<Longrightarrow> Q (s, h(p \<mapsto> q))) \<Longrightarrow> \<turnstile> P (@p := q) Q"
  by (auto simp: ht_def)

lemma sl_mutation_local: "\<turnstile> \<lbrace>e \<mapsto> - \<rbrace> @e := e' \<lbrace> e \<mapsto> e' \<rbrace>"
  by (auto simp: ht_def ex_singleton_def is_singleton_def)

lemma sl_mutation_local': "\<turnstile> \<lbrace>e \<mapsto> e'' \<rbrace> @e := e' \<lbrace> e \<mapsto> e' \<rbrace>"
  by (auto simp: ht_def is_singleton_def)

lemma sl_mutation_global: "\<turnstile> (\<lbrace>e \<mapsto> - \<rbrace> * r) @e := e' (\<lbrace> e \<mapsto> e' \<rbrace> * r)"
  apply (rule sl_frame)
  apply (rule local_mutation)
  by (rule sl_mutation_local)

lemma sl_mutation_backwards: "\<turnstile> (\<lbrace>e \<mapsto> - \<rbrace> * (\<lbrace> e \<mapsto> e' \<rbrace> -* p)) @e := e' p"
  apply (rule hl_weaken)
  prefer 3
  apply (rule sl_mutation_global)
  apply (rule mono_mutation)
  by (rule sep_impl_annil1)
  
lemma sl_cons_local: "stable_var v_update v \<Longrightarrow> \<turnstile> emp (`v := cons e) \<lbrace> `v \<mapsto> e \<rbrace>"
  by (auto simp add: ht_def emp_def new_comm_def is_singleton_def Let_def stable_var_def)

lemma sl_cons_global: "stable_var v_update v \<Longrightarrow> \<turnstile> r (`v := cons e) (\<lbrace> `v \<mapsto> e \<rbrace> * r)"
  apply (subst mult.left_neutral[symmetric])
  apply (rule sl_frame)
  apply (rule local_cons)
  by (rule sl_cons_local)

lemma sl_dispose_local: "\<turnstile> \<lbrace> e \<mapsto> - \<rbrace> dispose e emp"
  by (auto simp: emp_def dispose_comm_def ht_def ex_singleton_def is_singleton_def)

lemma sl_dispose_global: "\<turnstile> (\<lbrace>e \<mapsto> -\<rbrace> * r) dispose e r"
  apply (subst mult.left_neutral[symmetric]) back back back
  apply (rule sl_frame)
  apply (rule local_dispose)
  by (rule sl_dispose_local)

ML {*

val hoare_step_tac = 
  FIRST' [
      rtac @{thm sl_frame},
      rtac @{thm local_mutation},
      rtac @{thm sl_mutation_local'},
      rtac @{thm order_refl},
      rtac @{thm mono_seq},
      rtac @{thm mono_assign},
      rtac @{thm mono_mutation},
      rtac @{thm mono_dispose},
      rtac @{thm hl_assign}, 
      rtac @{thm sl_assign},
      rtac @{thm sl_mutation_global},
      rtac @{thm hl_if}, 
      rtac @{thm hl_skip}, 
      rtac @{thm hl_seq},
      rtac @{thm hl_while}
    ] 

val hoare_tac = REPEAT_ALL_NEW (CHANGED o hoare_step_tac)

*}

method_setup hoare_simp = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD (
    ALLGOALS (asm_full_simp_tac ctxt)
    THEN ALLGOALS hoare_tac 
    THEN ALLGOALS (asm_full_simp_tac ctxt)
  ))
*}

method_setup hoare_step = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD (
    ALLGOALS hoare_step_tac 
  ))
*}

method_setup hoare = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD (
    ALLGOALS hoare_tac
  ))
*}
end
