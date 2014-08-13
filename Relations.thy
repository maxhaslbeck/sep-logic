theory Relations
  imports Sets "Algebra/KAD"
begin

no_notation 
  pmult_one ("1")
  and times (infixl "*" 70)
  and sup (infixl "+" 65)

section {* Relations *}

typedef 'a relation = "UNIV :: 'a rel set" ..
setup_lifting type_definition_relation

instantiation relation :: (type) lattice
begin
lift_definition inf_relation :: "'a relation \<Rightarrow> 'a relation \<Rightarrow> 'a relation" is inf .
lift_definition sup_relation :: "'a relation \<Rightarrow> 'a relation \<Rightarrow> 'a relation" is sup .
lift_definition less_eq_relation :: "'a relation \<Rightarrow> 'a relation \<Rightarrow> bool" is less_eq .
lift_definition less_relation :: "'a relation \<Rightarrow> 'a relation \<Rightarrow> bool" is less .
instance 
  by default (transfer, auto)+
end

instantiation relation :: (type) bounded_lattice
begin
lift_definition bot_relation :: "'a relation" is bot .
lift_definition top_relation :: "'a relation" is top .
instance
  by default (transfer, auto)+
end

instantiation relation :: (type) complete_lattice
begin
lift_definition Inf_relation :: "'a relation set \<Rightarrow> 'a relation" is Inf .
lift_definition Sup_relation :: "'a relation set \<Rightarrow> 'a relation" is Sup .
instance
  by default (transfer, auto)+
end

instance relation :: (type) complete_distrib_lattice
  apply (default, simp_all add: SUP_def INF_def)
  by (transfer, auto)+

instantiation relation :: (type) dioid_one_zero
begin
lift_definition zero_relation :: "'a relation" is bot .
lift_definition one_relation :: "'a relation" is Id .
lift_definition times_relation :: "'a relation \<Rightarrow> 'a relation \<Rightarrow> 'a relation" is "op O" .
lift_definition plus_relation :: "'a relation \<Rightarrow> 'a relation \<Rightarrow> 'a relation" is sup .
instance
  by default (transfer, auto)+
end

instantiation relation :: (type) kleene_algebra
begin
lift_definition star_relation :: "'a relation \<Rightarrow> 'a relation" is rtrancl . 

instance
proof
  fix x y z :: "'a relation"
  show "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by transfer auto
  show "z + x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
    sorry
  show "z + y \<cdot> x \<le> y \<longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
    sorry
qed

end

lift_definition Id_on_rel :: "'a set \<Rightarrow> 'a relation" is Id_on .
lift_definition Domain_rel :: "'a relation \<Rightarrow> 'a set" is Domain .

interpretation REL: kad Id_on_rel Domain_rel
  by default (transfer, auto)+


end
