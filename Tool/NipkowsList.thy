theory NipkowsList
  imports "$ISABELLE_HOME/src/HOL/Hoare/SepLogHeap" Hoare
begin

no_notation Set.image (infixr "`" 90)
  and times (infixl "*" 70)

lemma is_singl_eq: "is_singleton x y h = (dom h = {x} & h x = Some y)"
  apply (auto simp: is_singleton_def)
  apply (metis domI domIff)
  by force

syntax
  "_list" :: "nat \<Rightarrow> nat list \<Rightarrow> bool" ("list _ _")

translations
  "list x xs" == "|CONST List | x xs"


lemma "\<turnstile> ( \<lbrace>p \<noteq> 0 \<rbrace> \<sqinter> \<lbrace> p \<mapsto> - \<rbrace> * \<lbrace>list q qs\<rbrace> ) 
    (@p := q) 
  \<lbrace> list p (p#qs) \<rbrace>"
apply hoare
apply clarify
apply (simp add: sep_conj_eq ex_singleton_def is_singl_eq ortho_def)
apply clarify
apply(subgoal_tac "p \<notin> set qs")
 prefer 2
 apply(blast dest:list_in_heap)
apply simp
done

record state =
  p :: nat
  q :: nat
  r :: nat

lemma "\<turnstile> ( \<lbrace> list `p Ps \<rbrace> * \<lbrace> list `q Qs \<rbrace> ) 
    while `p \<noteq> 0
    inv EXS ps qs. ( \<lbrace> list `p ps \<rbrace> * \<lbrace> list `q qs \<rbrace> ) \<sqinter> \<lbrace> rev ps @ qs = rev Ps @ Qs \<rbrace>
    do
      `r := `p;
      `p := @`p;
      @`r := `q;
      `q := `r
    od
  \<lbrace> list `q (rev Ps @ Qs) \<rbrace>"
  apply hoare
apply(auto simp add: sep_conj_eq ortho_def is_singl_eq)

apply (clarsimp simp add:List_non_null)
apply(rename_tac ps')
apply(rule_tac x = ps' in exI)
apply(rule_tac x = "(p a)#xa" in exI)
apply simp
apply(rule_tac x = "h1(p a:=None)" in exI)
apply(rule_tac x = "h2(p a \<mapsto> q a)" in exI)
apply simp
apply(rule conjI)
 apply(rule ext)
 apply(simp add:map_add_def split:option.split)
apply(rule conjI)
 apply blast
apply(simp add:map_add_def split:option.split)
apply(rule conjI)
apply(subgoal_tac "p a \<notin> set xa")
 prefer 2
 apply(blast dest:list_in_heap)
apply(simp)
apply fast

done

hide_const p q r

end
