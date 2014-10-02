theory State
  imports "Algebra/PartialMonoid"
begin

subsection {* Heap *}
type_synonym heap = "nat \<Rightarrow> nat option"

definition ortho :: "heap \<Rightarrow> heap \<Rightarrow> bool" (infix "\<bottom>" 55)
  where "h1 \<bottom> h2 \<equiv> dom h1 \<inter> dom h2 = {}"

interpretation partial_comm_monoid map_add ortho Map.empty
  by default (auto simp: ortho_def intro: map_add_comm)

definition heap_singleton :: "nat \<Rightarrow> nat \<Rightarrow> heap" where
  "heap_singleton v n \<equiv> \<lambda>x. if x = v then Some n else None"

definition heap_update :: "heap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> heap" where
  "heap_update h v n \<equiv> \<lambda>x. if x = v then Some n else h v"

lemma heap_upd_to_singl [simp]: "heap_update Map.empty v n = heap_singleton v n"
  by (simp add: heap_singleton_def heap_update_def)

primrec heap_update_list :: "heap \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> heap" where
  "heap_update_list h v [] = h"
| "heap_update_list h v (a#as) = heap_update_list (heap_update h v a) (Suc v) as"

lemma [simp]: "heap_update_list h v [n] = heap_update h v n"
  by (simp add: heap_update_list_def heap_update_def)

subsection {* State *}
type_synonym 'a state = "'a \<times> heap"

(* State Transformer *)
type_synonym 'a stateT = "'a state \<Rightarrow> 'a state"

definition insert_heap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a stateT" where
  "insert_heap f \<equiv> \<lambda>(s, h). (f s, h)"

definition insert_store :: "(heap \<Rightarrow> heap) \<Rightarrow> 'a stateT" where
  "insert_store f \<equiv> \<lambda>(s, h). (s, f h)"

(* State antiquotation *)
syntax
  "_quote" :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)" ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a" ("`_" [1000] 1000)

ML {*
  fun quote_tr [t] = Syntax_Trans.quote_tr @{syntax_const "_antiquote"} t
      | quote_tr ts = raise TERM ("quote_tr", ts)
*}

parse_translation {*
  [(@{syntax_const "_quote"}, K quote_tr)]
*}

end
