theory Semantics
  imports "Algebra/PartialMonoid" Sets Relations
begin

declare [[coercion_enabled]]

notation pmult_one ("1'")
no_notation times (infixl "*" 70)

section {* Heap *}

typedef heap = "UNIV :: (nat \<Rightarrow> nat option) set" ..
setup_lifting type_definition_heap

declare [[coercion Rep_heap]]

instantiation heap :: partial_comm_monoid
begin
lift_definition pmult_one_heap :: "heap" is Map.empty .
lift_definition pmult_heap :: "heap \<Rightarrow> heap \<Rightarrow> heap" is map_add .
lift_definition pmult_defined_heap :: "heap \<Rightarrow> heap \<Rightarrow> bool" is "\<lambda>h h'. dom h \<inter> dom h' = {}" .
instance
  by default (transfer, auto intro: map_add_comm)+
end

(* TODO: Null pointer is mapping to zero, we should add a bottom element in state *)
lift_definition heap_get :: "heap \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>h v. case (h v) of None \<Rightarrow> 0 | Some n \<Rightarrow> n" .

lift_definition heap_update :: "heap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> heap" is
  "\<lambda>h v n x. if x = v then Some n else h v" .

lifting_forget heap.lifting

section {* State *}

type_synonym store = "string \<Rightarrow> nat"

typedef state = "UNIV :: (store \<times> heap) set" ..
setup_lifting type_definition_state

instantiation state :: partial_ab_semigroup
begin
lift_definition pmult_state :: "state \<Rightarrow> state \<Rightarrow> state" is "\<lambda>(s, h) (s', h'). (sup s s', h * h')" .
lift_definition pmult_defined_state :: "state \<Rightarrow> state \<Rightarrow> bool" is "\<lambda>(s, h) (s', h'). h ## h'" .

instance
  apply default
  apply transfer
  apply auto
apply (metis pmult_def_eq)
apply (metis pmult_def_eq)
apply transfer
apply auto
apply (metis inf_sup_aci(6))
apply (metis partial_semigroup_class.pmult_assoc)
apply transfer
apply auto
apply (metis pmult_comm_def)
apply transfer
apply auto
apply (metis sup_commute)
by (metis pmult_comm)

end

instantiation state :: partial_comm_monoid
begin
lift_definition pmult_one_state :: "state" is "(bot, 1')" .

instance
  apply default
  apply transfer
  apply auto
  apply transfer
  apply auto
apply (metis bot.extremum sup_absorb1)
by (metis pmult_oner)
end

section {* Semantics of a Simple While Programming Language *}

definition store_update :: "string \<Rightarrow> nat \<Rightarrow> store \<Rightarrow> store" where
  "store_update v n s \<equiv> \<lambda>x. if x = v then n else s x"

lift_definition state_update :: "string \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" is 
  "\<lambda>v n (s, h). (store_update v n s, h)" .

lift_definition get_store_value :: "state \<Rightarrow> string \<Rightarrow> nat" is "\<lambda>(s, h) v. s v" .

lift_definition heap_lookup :: "string \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" is 
  "\<lambda>v n (s, h). (store_update v (heap_get h n) s, h)" .

lift_definition heap_mutation :: "nat \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" is "\<lambda>m n (s, h). (s, heap_update h m n)" .

type_synonym comm = "state relation"

lift_definition fun_relation :: "(state \<Rightarrow> state) \<Rightarrow> state relation" is "\<lambda>f. {(x, f x) | x. True}" .

definition assign :: "string \<Rightarrow> nat \<Rightarrow> comm" where 
  "assign v n \<equiv> fun_relation (state_update v n)"

definition lookup :: "string \<Rightarrow> nat \<Rightarrow> comm" where
  "lookup v n \<equiv> fun_relation (heap_lookup v n)"

definition mutation :: "nat \<Rightarrow> nat \<Rightarrow> comm" where
  "mutation m n \<equiv> fun_relation (heap_mutation m n)"

end
