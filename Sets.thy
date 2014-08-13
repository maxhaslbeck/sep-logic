theory Sets
  imports "Algebra/PartialMonoid" "Algebra/BBI"
begin

section {* Resource Predicates *}

text {* A resource predicate is a set on a partial monoid. *}

text {* The powerset lifting of a partial semigroup form a quantale *}

instantiation "set" :: (partial_semigroup) near_quantale_Sup
begin
definition "P \<cdot> Q \<equiv> {x * y | x y. x ## y \<and> x \<in> P \<and> y \<in> Q}"

instance
  apply (default, auto simp: times_set_def)
  apply (metis partial_semigroup_class.pmult_assoc partial_semigroup_class.pmult_def)
  by (metis partial_semigroup_class.pmult_assoc partial_semigroup_class.pmult_def)
end

instance "set" :: (partial_semigroup) pre_quantale_Sup
  by default (auto simp: times_set_def)

instance "set" :: (partial_semigroup) quantale_Sup
  by default (auto simp: times_set_def)

text {* Unit, commutativity and distributivity are also lifted. *}

instantiation "set" :: (partial_monoid) near_quantale_Sup_unital
begin
definition "one_set \<equiv> {pmult_one}"
instance
  by default (auto simp: times_set_def one_set_def pmult_oner pmult_onel)
end

instance "set" :: (partial_ab_semigroup) comm_quantale_Sup
  apply (default, auto simp: times_set_def)
  by (metis pmult_comm pmult_comm_def)+

instance "set" :: (partial_monoid) quantale_Sup_unital ..

instance "set" :: (partial_comm_monoid) comm_quantale_Sup_unital 
  by default auto

instance "set" :: (partial_semigroup) distrib_quantale_Sup ..

instance "set" :: (partial_comm_monoid) distrib_comm_quantale_Sup_unital ..

instance "set" :: (partial_comm_monoid) bbi ..

end
