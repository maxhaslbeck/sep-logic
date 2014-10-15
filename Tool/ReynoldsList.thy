theory ReynoldsList
  imports Refinement
begin

no_notation pmult (infixl "*" 80)
  and times (infixl "*" 70)
  and Set.image (infixr "`" 90)
  and sup (infixl "+" 65)
  and pmult_one ("1")
  and bot ("\<bottom>")
  and sep_impl (infix "-*" 55)

no_notation Set.image (infixr "`" 90)
  and times (infixl "*" 70)

(* List *)
primrec list' :: "nat \<Rightarrow> nat list \<Rightarrow> 'a pred" where
  "list' i [] = \<lbrace>i = 0\<rbrace> \<sqinter> emp"
| "list' i (y#ys) = \<lbrace>i \<noteq> 0\<rbrace> \<sqinter> (EXS j. \<lbrace>i [\<mapsto>] [y,j]\<rbrace> * list' j ys)"

syntax
  "_list" :: "nat \<Rightarrow> nat list \<Rightarrow> bool" ("list _ _")

translations
  "list x xs" == "|(`(CONST curry (CONST list' x xs)))|"

lemma empty_list: "list' i a (s, h) \<Longrightarrow> i = 0 \<Longrightarrow> a = []"
  by (metis (mono_tags, lifting) PairE inf1E list'.simps(2) list.exhaust old.prod.case)

lemma list_i_null: "list' 0 a (s, h) \<Longrightarrow> a = [] \<and> h = Map.empty"
  by (induct a, simp_all add: emp_def)

lemma list_i_not_null: "list' i a (s, h) \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> a \<noteq> []"
  by (induct a, simp_all add: emp_def)

lemma list_i_not_null_var: "list' i x (s, h) \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> (\<exists>y ys. x = y#ys)"
  apply (auto dest!: list_i_not_null)
  by (metis list.exhaust)

lemma sep_conj_s_preserving: 
  assumes "(\<And>h. P (s, h) \<Longrightarrow> P (s', h))" and  "(\<And>h. Q (s, h) \<Longrightarrow> Q (s', h))" 
  shows "((P * Q) (s, h) \<Longrightarrow> (P * Q) (s', h))"
  using assms by (auto simp add: sep_conj_def ortho_def split: option.splits) 

lemma list_s_preserving: "list' n as (s :: 'a, h) \<Longrightarrow> list' n as (s' :: 'a, h)"
  apply (induct as arbitrary: n h)
  by (auto simp add: emp_def intro: sep_conj_s_preserving [of _ s])

record list_state =
  i :: nat
  j :: nat
  k :: nat

lemma [simp]: "list' n as (i_update m s, h) = list' n as (s, h)"
  by (auto intro: list_s_preserving)

lemma [simp]: "list' n as (j_update m s, h) = list' n as (s, h)"
  by (auto intro: list_s_preserving)

lemma [simp]: "list' n as (k_update m s, h) = list' n as (s, h)"
  by (auto intro: list_s_preserving)

lemma heap_div: "h1 \<bottom> h2 \<Longrightarrow> h1 a = Some b \<Longrightarrow> (h1 ++ h2) a = Some b"
  apply (auto simp: ortho_def)
  by (auto simp: map_add_def split: option.splits)

lemma heap_div_var: "h1 \<bottom> h2 \<Longrightarrow> h2 a = Some b \<Longrightarrow> (h1 ++ h2) a = Some b"
  by (auto simp: ortho_def)

lemma heap_div_the: "h1 \<bottom> h2 \<Longrightarrow> h1 a = Some b \<Longrightarrow> the ((h1 ++ h2) a) = b"
  apply (auto simp: ortho_def)
  by (auto simp: map_add_def split: option.splits)
  
lemma [iff]: "(\<lambda>(s, h). True) = true"
  by auto

lemma [iff]: "x \<sqinter> emp = (\<lambda>(s, h). x (s, h) \<and> emp (s, h))"
  by auto

lemma "q s \<Longrightarrow> (p \<sqinter> q) s = p s \<and> q s"
  by auto

lemma pred_infI: "p s \<and> q s \<Longrightarrow> (p \<sqinter> q) s"
  by auto

lemma pred_infD: "(p \<sqinter> q) s \<Longrightarrow> p s \<and> q s"
  by auto

lemma listI: "p \<noteq> 0 \<Longrightarrow>  h1 \<bottom> h2 \<Longrightarrow> is_heap_list p [q, r] (s, h1) \<Longrightarrow> list' r ns (s, h2) \<Longrightarrow> list' p (q#ns) (s, h1 ++ h2)"
  by (force simp: sep_conj_eq)

declare sep_conj_eq [simp] emp_def[simp]
notation 
  pred_ex (binder "\<exists> " 10)
  and inf (infixl "\<and>" 75)

lemma "\<lbrakk>\<lbrace>list `i Ao\<rbrace> , \<lbrace> list `j (rev Ao)\<rbrace>\<rbrakk> \<sqsubseteq>
    `j := 0;
    while `i \<noteq> 0
    do
      `k := @(`i + 1);
      @(`i + 1) := `j;
      `j := `i;
      `i := `k
    od" 
proof -
  have "\<lbrakk> \<lbrace>list `i Ao\<rbrace>, \<lbrace>list `j (rev Ao)\<rbrace> \<rbrakk> \<sqsubseteq> 
      `j := 0; 
      \<lbrakk>\<exists>A B. (\<lbrace> list `i A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ B \<rbrace>, 
        \<lbrace> list `j (rev Ao) \<rbrace> \<rbrakk>" 
      (is "... \<sqsubseteq> ?p")
    by refinement force
  also have "?p \<sqsubseteq> 
        `j := 0;
        while `i \<noteq> 0 do
          \<lbrakk>(\<exists>A B. (\<lbrace> list `i A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ B \<rbrace>) \<and> \<lbrace>`i \<noteq> 0\<rbrace>, 
            \<exists>A B. (\<lbrace> list `i A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ B \<rbrace>\<rbrakk>
        od" (is "... \<sqsubseteq> ?p")
    by refinement (auto dest!: list_i_null)
  also have "?p \<sqsubseteq> 
        `j := 0;
        while `i \<noteq> 0 do
          \<lbrakk>(\<exists>a A B k. (\<lbrace>`i [\<mapsto>] [a,k]\<rbrace> * \<lbrace> list k A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev (a#A)) @ B \<rbrace>) \<and> \<lbrace>`i \<noteq> 0\<rbrace>, 
            \<exists>A B. (\<lbrace> list `i A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ B \<rbrace>\<rbrakk>
        od" (is "... \<sqsubseteq> ?p")
    by refinement (frule list_i_not_null_var, fastforce+)
  also have "?p \<sqsubseteq> 
        `j := 0;
        while `i \<noteq> 0 do
          `k := @(`i + 1);
          \<lbrakk>(\<exists> a A B. (\<lbrace>`i [\<mapsto>] [a,`k]\<rbrace> * \<lbrace> list `k A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev (a#A)) @ B \<rbrace>) \<and> \<lbrace>`i \<noteq> 0\<rbrace>, 
            \<exists> A B. (\<lbrace> list `i A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ B \<rbrace>\<rbrakk>
        od" (is "... \<sqsubseteq> ?p")
    apply refinement  
    apply (rule_tac x=x in exI, rule_tac x=xa in exI, rule_tac x=xb in exI)
    apply (subgoal_tac "the ((h1a ++ h2a ++ h2) (Suc (i a))) = xc")
    by (auto simp add: is_singleton_def intro!: heap_div_the heap_divider)
  also have "?p \<sqsubseteq> 
        `j := 0;
        while `i \<noteq> 0 do
          `k := @(`i + 1);
          @(`i + 1) := `j;
          \<lbrakk>(\<exists> a A B. (\<lbrace>`i [\<mapsto>] [a,`j]\<rbrace> * \<lbrace> list `k A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev (a#A)) @ B \<rbrace>) \<and> \<lbrace>`i \<noteq> 0\<rbrace>, 
            \<exists> A B. (\<lbrace> list `i A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ B \<rbrace>\<rbrakk>
        od" (is "... \<sqsubseteq> ?p")
    by refinement (auto simp: spec_def ht_def)
  also have "?p \<sqsubseteq> 
        `j := 0;
        while `i \<noteq> 0 do
          `k := @(`i + 1);
          @(`i + 1) := `j;
          \<lbrakk>(\<exists>a A B. (\<lbrace> list `k A \<rbrace> * \<lbrace>`i [\<mapsto>] [a,`j]\<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev (a#A)) @ B \<rbrace>) \<and> \<lbrace>`i \<noteq> 0\<rbrace>, 
            \<exists>A B. (\<lbrace> list `i A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ B \<rbrace>\<rbrakk>
        od" (is "... \<sqsubseteq> ?p")
    by refinement (subst mult_commute, force)
  also have "?p \<sqsubseteq> 
        `j := 0;
        while `i \<noteq> 0 do
          `k := @(`i + 1);
          @(`i + 1) := `j;
          \<lbrakk>(\<exists>a A B. (\<lbrace> list `k A \<rbrace> * \<lbrace> list `i (a#B) \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ (a#B) \<rbrace>) \<and> \<lbrace>`i \<noteq> 0\<rbrace>, 
            \<exists>A B. (\<lbrace> list `i A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ B \<rbrace>\<rbrakk>
        od" (is "... \<sqsubseteq> ?p")
    apply refinement
    apply (rule_tac x=x in exI, rule_tac x=xa in exI, rule_tac x=xb in exI)
    apply (auto simp only: sep_conj_eq)
    apply (rule_tac x=h1a in exI, rule_tac x="h2a ++ h2" in exI)
    apply (auto simp del: list'.simps is_heap_list.simps intro!: listI)
    apply (force simp add: is_singleton_def ortho_def)
    by (force simp add: is_singleton_def ortho_def intro: listI)
  also have "?p \<sqsubseteq> 
        `j := 0;
        while `i \<noteq> 0 do
          `k := @(`i + 1);
          @(`i + 1) := `j;
          \<lbrakk>(\<exists>A B. (\<lbrace> list `k A \<rbrace> * \<lbrace> list `i B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ B \<rbrace>) \<and> \<lbrace>`i \<noteq> 0\<rbrace>, 
            \<exists>A B. (\<lbrace> list `i A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ B \<rbrace>\<rbrakk>
        od" (is "... \<sqsubseteq> ?p")
    by refinement (force simp only: sep_conj_eq)
  also have nine: "?p \<sqsubseteq> 
        `j := 0;
        while `i \<noteq> 0 do
          `k := @(`i + 1);
          @(`i + 1) := `j;
          `j := `i;
          \<lbrakk>(\<exists>A B. (\<lbrace> list `k A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ B \<rbrace>) \<and> \<lbrace>`i \<noteq> 0\<rbrace>, 
            \<exists>A B. (\<lbrace> list `i A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ B \<rbrace>\<rbrakk>
        od" (is "... \<sqsubseteq> ?p")
    by refinement auto
  also have ten: "?p \<sqsubseteq> 
        `j := 0;
        while `i \<noteq> 0 do
          `k := @(`i + 1);
          @(`i + 1) := `j;
          `j := `i;
          `i := `k
        od"
        by refinement auto
  finally show ?thesis .
qed


lemma "\<turnstile> \<lbrace>list `i Ao\<rbrace>
      `j := 0;
      while `i \<noteq> 0
      inv \<exists>A B. (\<lbrace> list `i A \<rbrace> * \<lbrace> list `j B \<rbrace>) \<and> \<lbrace>(rev Ao) = (rev A) @ B \<rbrace>
      do
        `k := @(`i + 1);
        @(`i + 1) := `j;
        `j := `i;
        `i := `k
      od
   \<lbrace> list `j (rev Ao)\<rbrace>" 
apply hoare
apply (clarsimp dest!: list_i_null)
prefer 2
apply force
apply clarsimp
apply (frule list_i_not_null_var, simp)
apply (clarsimp simp add: is_singleton_def)
apply (rule_tac x=ys in exI, rule_tac x="y # xa" in exI)
apply (subgoal_tac "the (([i a \<mapsto> y, Suc (i a) \<mapsto> x] ++ h2a ++ h2) (Suc (i a))) = x")
apply auto
prefer 2
apply (force intro!: heap_div_the heap_divider)
apply (rule_tac x=h2a in exI, rule_tac x="[i a \<mapsto> y, Suc (i a) \<mapsto> j a] ++ h2" in exI)
apply (auto simp add: is_singleton_def ortho_def intro!: listI)
by (metis domIff empty_map_add fun_upd_upd map_add_upd_left)

hide_const i j k


lemma "\<turnstile> ( \<lbrace> x [\<mapsto>] [b, j] \<rbrace> * \<lbrace> list i as \<rbrace> ) @x := a ( \<lbrace> x [\<mapsto>] [a, j] \<rbrace> * \<lbrace> list i as \<rbrace> )"
  by (simp only: is_heap_list.simps(2) curry_conv split_eta) hoare


end
