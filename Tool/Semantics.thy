theory Semantics
  imports "../Algebra/PartialMonoid" "../Algebra/BBI"
begin

section {* Notation and types *}

no_notation pmult (infixl "*" 80)
  and times (infixl "*" 70)
  and Set.image (infixr "`" 90)
  and sup (infixl "+" 65)
  and pmult_one ("1")
  and bot ("\<bottom>")
  and sep_impl (infix "-*" 55)

type_synonym heap = "nat \<Rightarrow> nat option"
type_synonym 'a state = "'a \<times> heap"
type_synonym 'a stateT = "'a state \<Rightarrow> 'a state"
type_synonym 'a pred = "'a state \<Rightarrow> bool"
type_synonym 'a state_predT = "'a state \<Rightarrow> 'a pred"
type_synonym 'a predT = "'a pred \<Rightarrow> 'a pred"


section {* Heap *}

definition ortho :: "heap \<Rightarrow> heap \<Rightarrow> bool" (infix "\<bottom>" 55)
  where "h1 \<bottom> h2 \<equiv> dom h1 \<inter> dom h2 = {}"

lemma theI: "h x = Some y \<Longrightarrow> the (h x) = y"
  by simp

lemma heap_divider: "h1 \<bottom> h2 \<Longrightarrow> h1 x = Some y \<Longrightarrow> (h1 ++ h2) x = Some y"
  by (auto simp: ortho_def map_add_def split: option.splits)

lemma heap_add_comm: "h1 \<bottom> h2 \<Longrightarrow> h1 ++ h2 = h2 ++ h1"
  by (auto simp: ortho_def intro: map_add_comm)

(* should write this directly on ML *)
definition heap_update :: "nat \<Rightarrow> nat \<Rightarrow> heap \<Rightarrow> heap" where
  "heap_update p q h \<equiv> h (p\<mapsto>q)"
declare heap_update_def[simp]

interpretation partial_comm_monoid map_add ortho Map.empty
  by default (auto simp: ortho_def intro: map_add_comm)

section {* Predicates *}

definition emp :: "'a pred" where "emp \<equiv> \<lambda>(s, h). h = Map.empty"

definition sep_conj :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a pred" (infixl "*" 75) where
  "P * Q \<equiv> \<lambda>(s, h). \<Squnion> {P (s, h1) \<and> Q (s, h2) | h1 h2. h = h1 ++ h2 \<and> ortho h1 h2}"

lemma sep_conj_eq: "(P * Q) (s, h) = (\<exists>h1 h2. h = h1++h2 \<and> (ortho h1 h2) \<and> P (s, h1) \<and> Q (s, h2))"
  by (auto simp: sep_conj_def)

lemma sep_conj_eq2: "(P * Q) = (\<lambda>(s, h). (\<exists>h1 h2. h = h1++h2 \<and> (ortho h1 h2) \<and> P (s, h1) \<and> Q (s, h2)))"
  by (auto simp: sep_conj_def)

abbreviation (input)
  pred_ex :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "EXS " 10) where
  "EXS x. P x \<equiv> \<lambda>s. \<exists>x. P x s"

abbreviation (input)
  pred_all :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "ALLS " 10) where
  "ALLS x. P x \<equiv> \<lambda>s. \<forall>x. P x s"

abbreviation true :: "'a pred" where "true \<equiv> top" 
abbreviation false :: "'a pred" where "false \<equiv> bot"

(* Algebraic structure *)
interpretation comm_monoid_mult sep_conj emp
  apply default
  apply (auto simp add: emp_def sep_conj_def ortho_def intro!: ext)
  apply (rule_tac x=h1a in exI, simp)
  apply (rule_tac x="h2a ++ h2" in exI, auto)
  apply (rule_tac x=h2a in exI, auto)
  apply (rule_tac x="h1 ++ h1a" in exI, auto)
  apply (rule_tac x=h2a in exI, auto)
  by (auto intro: map_add_comm)

interpretation quantale_Sup Inf Sup inf less_eq less sup bot top sep_conj
  by default (auto simp: sep_conj_def)

interpretation bbi Inf Sup inf less_eq less sup bot top minus uminus sep_conj emp
  by default (auto simp: sep_conj_def emp_def)

abbreviation magic_wand :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a pred" (infix "-*" 55) where 
  "P -* Q \<equiv> sep_impl P Q"

lemma magic_wand: "(P -* Q) = (\<lambda>(s, h). (\<forall>h'. h' \<bottom> h \<and> P (s, h') \<longrightarrow> Q(s, h ++ h')))"
  oops
  
(* Predicates about heaps *)
definition is_singleton :: "nat \<Rightarrow> nat \<Rightarrow> heap \<Rightarrow> bool" where
  "is_singleton e t h \<equiv> h = [e \<mapsto> t]"

definition ex_singleton :: "nat \<Rightarrow> heap \<Rightarrow> bool" where
  "ex_singleton e h \<equiv> \<exists>t. is_singleton e t h"

primrec is_heap_list :: "nat \<Rightarrow> nat list \<Rightarrow> 'a pred" where
  "is_heap_list e [] = emp"
| "is_heap_list e (t#ts) = (\<lambda>(s, h). is_singleton e t h) * is_heap_list (Suc e) ts"

section {* Predicate Transformers *}

(* Algebraic Structure *)
interpretation PT: monoid "op o" id
  by default auto

interpretation PT: near_quantale_Sup Inf Sup inf less_eq less sup bot "top :: 'a predT" "op o"
  by default auto

interpretation PT: near_quantale_Sup_unital id "op o" Inf Sup inf less_eq less sup bot "top :: 'a predT"
  by default auto

interpretation PT: pre_quantale_Sup Inf Sup inf less_eq less sup bot "top :: 'a predT" "op o"
  (* nitpick *) oops

interpretation PT: quantale_Sup_unital id "op o" Inf Sup inf less_eq less sup bot top
  (* nitpick *) oops

interpretation PT: complete_distrib_lattice Inf Sup inf less_eq less sup bot "top :: 'a predT" ..

section {* Lifting between types *}

definition lift_stateT_pred :: "'a stateT \<Rightarrow> 'a state_predT" where
  "lift_stateT_pred f \<equiv> \<lambda>\<sigma> \<sigma>'. \<sigma>' = f \<sigma>"

definition lift_state_pred_predT :: "'a state_predT \<Rightarrow> 'a predT" where
  "lift_state_pred_predT F \<equiv> \<lambda>Q \<sigma>. F \<sigma> \<le> Q"

definition lift_state_a_stateT :: "('a state \<Rightarrow> 'a) \<Rightarrow> 'a stateT" where
  "lift_state_a_stateT F \<equiv> \<lambda>(s, h). (F (s, h), h)"

definition lift_state_heap_stateT :: "('a state \<Rightarrow> heap) \<Rightarrow> 'a stateT" where
  "lift_state_heap_stateT F \<equiv> \<lambda>(s, h). (s, F (s, h))"

definition lift_stateT_predT :: "'a stateT \<Rightarrow> 'a predT" ("<_>") where
  "<f> \<equiv> \<lambda>Q. Q o f"

definition lift_state_a_predT :: "('a state \<Rightarrow> 'a) \<Rightarrow> 'a predT" where
  "lift_state_a_predT F \<equiv> < lift_state_a_stateT F >"

definition lift_state_heap_predT :: "('a state \<Rightarrow> heap) \<Rightarrow> 'a predT" where
  "lift_state_heap_predT F \<equiv> < lift_state_heap_stateT F >"

definition lift_pred_predT :: "'a pred \<Rightarrow> 'a predT" ("\<lceil>_\<rceil>") where
  "\<lceil>P\<rceil> \<equiv> \<lambda>Q. - P \<squnion> Q"

declare lift_state_a_predT_def [simp]
  lift_state_heap_predT_def [simp]
  lift_stateT_predT_def [simp]
  lift_state_a_stateT_def [simp]
  lift_state_heap_stateT_def [simp]
  lift_pred_predT_def [simp]

section {* Simple while language with pointers *}

abbreviation skip :: "'a predT" ("skip") where "skip \<equiv> id"

notation comp (infixl ";" 60)

abbreviation iteration :: "'a predT \<Rightarrow> 'a predT" ("_\<^sup>\<star>" [1000] 1000) where
  "F\<^sup>\<star> \<equiv> near_quantale_unital.qstar Sup op \<circ> id F"

definition if_comm :: "'a pred \<Rightarrow> 'a predT \<Rightarrow> 'a predT \<Rightarrow> 'a predT" where
  "if_comm p x y = \<lceil>p\<rceil>;x \<squnion> \<lceil>-p\<rceil>;y"

definition while_comm :: "'a pred \<Rightarrow> 'a predT \<Rightarrow> 'a predT" where
  "while_comm p x = (\<lceil>p\<rceil>;x)\<^sup>\<star>;\<lceil>-p\<rceil>"

definition while_inv_comm :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a predT \<Rightarrow> 'a predT" where
  "while_inv_comm p i x = (\<lceil>p\<rceil>;x)\<^sup>\<star>;\<lceil>-p\<rceil>"

syntax
  "_quote" :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)" ("(\<lbrace>_\<rbrace>)" [0] 1000)       (* Create assertion applying antiquotes *)
  "_antiquote_s" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a" ("`_" [1000] 1000) (* Apply store *)
  "_antiquote_to_h" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a" ("@_" [1000] 1000) (* Apply to heap *)
  "_antiquote_h" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a" ("|_|" [1000] 1000) (* Apply heap *)
  "_assign" :: "idt \<Rightarrow> 'b \<Rightarrow> 'a predT" ("(`_ :=/ _)" [70, 65] 61)
  "_mutation" :: "'b \<Rightarrow> 'b \<Rightarrow> 'a predT" ("(@_ :=/ _)" [70, 65] 61)
  "_subst" :: "'a pred \<Rightarrow> 'b \<Rightarrow> idt \<Rightarrow> 'a pred" ("_[_'/`_]" [1000] 999)
  "_if" :: "'a pred \<Rightarrow> 'a predT \<Rightarrow> 'a predT \<Rightarrow> 'a predT" ("(0if _//then _//else _//fi)" [0,0,0] 61)
  "_if_skip" :: "'a pred \<Rightarrow> 'a predT \<Rightarrow> 'a predT" ("(0if _//then _//fi)" [0,0] 61)
  "_while" :: "'a pred \<Rightarrow> 'a predT \<Rightarrow> 'a predT" ("(0while  _//do _//od)" [0, 0] 61)
  "_while_inv" :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a predT \<Rightarrow> 'a predT" ("(0while _//inv _//do _//od)" [0, 0, 0] 61)

ML_file "while_syntax.ML"

parse_translation {*
  [(@{syntax_const "_quote"}, K quote_tr'),
    (@{syntax_const "_subst"}, K subst_tr),
    (@{syntax_const "_assign"}, K assign_tr),
    (@{syntax_const "_mutation"}, K mutation_tr),
    (@{syntax_const "_if"}, K if_tr), 
    (@{syntax_const "_while"}, K while_tr), 
    (@{syntax_const "_while_inv"}, K while_inv_tr)]
*}

translations
  "if b then x fi" == "if b then x else skip fi"

(* Syntactic sugar of predicates about heap *)
syntax
  "_is_singl" :: "nat \<Rightarrow> nat \<Rightarrow> bool" ("_ \<mapsto> _" [56,51] 56)
  "_ex_singleton" :: "nat \<Rightarrow> bool" ("_ \<mapsto> -" [56] 56)
  "_is_heap_list" :: "nat \<Rightarrow> nat \<Rightarrow> bool" ("_ [\<mapsto>] _" [56,51] 56)

translations
  "i \<mapsto> j" == "|(CONST is_singleton i j)|"
  "i \<mapsto> -" == "|(CONST ex_singleton i)|"
  "x [\<mapsto>] xs" == "|(`(CONST curry (CONST is_heap_list x xs)))|"


section {* Monotonicity *}

text {* All the constructs are monotones. *}

lemma mono_skip: "mono skip"
  by (simp add: mono_def)

lemma mono_assign: "mono ( `x := ` |m| )"
  by (auto simp: mono_def)

lemma mono_mutation: "mono ( @`x := `m )"
  by (auto simp: mono_def)

lemma mono_seq: "mono F \<Longrightarrow> mono G \<Longrightarrow> mono (F o G)"
  by (auto simp: mono_def)

lemma mono_if: "mono F \<Longrightarrow> mono G \<Longrightarrow> mono (if_comm p F G)"
  by (auto simp: if_comm_def mono_def)

lemma mono_Sup: "\<forall>(f :: 'a :: complete_lattice \<Rightarrow> 'a) \<in> F. mono f  \<Longrightarrow> mono (\<Squnion>F)"
  by (auto simp: mono_def, rule SUP_mono) auto

lemma mono_qpower: "mono F \<Longrightarrow> mono (PT.Sup.qpower F i)"
  apply (induct_tac i)
  apply (unfold mono_def)
  by simp_all

lemma mono_iteration: "mono F \<Longrightarrow> mono F\<^sup>\<star>"
  apply (subst PT.Sup.qstar_def)
  apply (rule mono_Sup[of "{y. \<exists>i. y = near_quantale_unital.qpower op \<circ> skip F i}"])
  by (auto intro: mono_qpower)

lemma mono_while: "mono F \<Longrightarrow> mono (while_comm p F)"
  apply (auto simp: while_comm_def intro!: mono_seq mono_iteration)
  by (auto simp: mono_def)

section {* Locality *}

definition local :: "'a predT \<Rightarrow> bool" where
  "local F \<equiv> \<forall>x y. F x * y \<le> F (x * y)"

text {* All the constructs are local *}

lemma local_skip: "local skip"
  by (simp add: local_def)

lemma local_seq: "mono F \<Longrightarrow> local F \<Longrightarrow> local G \<Longrightarrow> local (F o G)"
proof (subst local_def, (rule allI)+, (subst comp_apply)+)
  fix x y assume assms: "mono F" "local F" "local G"
  hence "F (G x) * y \<le> F (G x * y)"
    by (simp add: local_def)
  also have "... \<le> F (G (x * y))" using assms
    by (auto simp add: assms local_def mono_def)
  finally show "F (G x) * y \<le> F (G (x * y))" .
qed

lemma local_if: "local F \<Longrightarrow> local G \<Longrightarrow> local (if_comm p F G)"
  by (auto simp: if_comm_def local_def)

lemma local_power: "mono F \<Longrightarrow> local F \<Longrightarrow> local (near_quantale_unital.qpower op \<circ> skip F i)"
  apply (induct i)
  by (auto simp: local_skip intro: local_seq)

lemma local_mutation: "local (@e := e')"
sorry

lemma local_sup: "local f \<Longrightarrow> local g \<Longrightarrow> local (f \<squnion> g)"
proof (subst local_def, (rule allI)+, simp)
  fix x y assume assms: "local f" "local g"
  have "(f x \<squnion> g x) * y \<le> f x * y \<squnion> g x * y"
    by (metis Semantics.Sup.qdistr eq_refl)
  also have "... \<le>  f (x * y) \<squnion> g (x * y)" using assms
    apply (unfold local_def)
    by (metis sup.mono)
  finally show "(f x \<squnion> g x) * y \<le> f (x * y) \<squnion> g (x * y)" .
qed

lemma local_Sup: "\<forall>f \<in> F. local f \<Longrightarrow> local (\<Squnion>F)"
  apply (subst local_def)
  apply (rule allI)+
  apply simp
  apply (unfold SUP_def)
  apply (subst Semantics.Sup.Join_distr)
  apply simp
  apply (rule SUP_mono)
  apply (rule_tac x=xa in bexI)
  by (auto simp: local_def)

lemma local_iteration: "mono F \<Longrightarrow> local F \<Longrightarrow> local F\<^sup>\<star>"
  apply (simp add: PT.Sup.qstar_def)
  apply (rule local_Sup[of "{y. \<exists>i. y = near_quantale_unital.qpower op \<circ> skip F i}"])
  by (auto intro: local_power)

lemma local_while: "mono F \<Longrightarrow> local (op \<squnion> p) \<Longrightarrow> local F \<Longrightarrow> local (while_comm p F)"
  apply (simp add: while_comm_def)
  apply (auto intro!: local_seq local_iteration mono_iteration mono_seq)
  apply (auto simp: mono_def)
oops

end
