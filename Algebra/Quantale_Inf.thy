theory Quantale_Inf
  imports Abstract_Quantales
begin

no_notation 
  times (infixl "*" 70) and
  plus (infixl "+" 65) 
  
notation 
  sup (infixl "+" 65) and
  inf (infixl "\<sqinter>" 70) and
  Sup ("\<Squnion>_" [900] 900) and
  Inf ("\<Sqinter>_" [900] 900) and
  top ("\<top>") and
  bot ("\<bottom>") and
  times (infixl "\<cdot>" 70) 

sublocale complete_lattice \<subseteq> Inf!: abs_complete_lattice Inf
  where [simp]: "abs_complete_lattice.join Inf = op \<sqinter>"
    and [simp]: "abs_complete_lattice.less_eq Inf = op \<ge>"
    and [simp]: "abs_complete_lattice.less Inf = op >"
    and [simp]: "abs_complete_lattice.Meet Inf = Sup"
    and [simp]: "abs_complete_lattice.meet Inf = op +"
    and [simp]: "abs_complete_lattice.top Inf = \<bottom>"
    and [simp]: "abs_complete_lattice.bot Inf = \<top>"
proof -
  show "abs_complete_lattice Inf"
    apply unfold_locales
    apply (metis Inf_atLeastAtMost atLeastAtMost_singleton_iff order_refl)
    apply (auto simp: Inf_le_iff intro!: Inf_eqI Inf_greatest)
    apply (metis (mono_tags) Inf_lower UnionI)
    apply (metis le_Inf_iff)
    by (metis Inf_greatest inf_commute le_iff_inf)
  then interpret cs: abs_complete_lattice Inf .
  show "cs.join = op \<sqinter>"
    by (default, default) (simp add: cs.join_def)
  show [simp]: "cs.less_eq = op \<ge>"
    apply (default, default)
    apply (auto simp: cs.less_eq_def cs.join_def)
    apply (metis inf_le1)
    by (metis inf_absorb2)
  show "cs.less = op >"
    apply (default, default)
    by (auto simp add: less_le_not_le cs.less_def)
  show [simp]: "cs.Meet = Sup"
    by default (auto simp add: cs.Meet_def Sup_Inf)
  show "cs.meet = op +"
    by (default, default) (simp add: cs.meet_def)
  show "cs.top = \<bottom>"
    by (simp add: cs.top_def)
  show "cs.bot = \<top>"
    by (simp add: cs.bot_def)
qed

class near_quantale_Inf = complete_lattice + semigroup_mult +
  assumes qInf_distr: "\<Sqinter> Y \<cdot> x = \<Sqinter> ((\<lambda>y. y \<cdot> x) ` Y)"

class near_quantale_Inf_unital = near_quantale_Inf + monoid_mult

class pre_quantale_Inf = near_quantale_Inf + 
  assumes qInf_subdistl: "x \<cdot> \<Sqinter> Y \<le> \<Sqinter> ((\<lambda>y. x \<cdot> y) ` Y)"

class quantale_Inf = pre_quantale_Inf +
  assumes qInf_supdistl: "\<Sqinter> ((\<lambda>y. x \<cdot> y) ` Y) \<le> x \<cdot> \<Sqinter> Y"

class quantale_Inf_unital = quantale_Inf + monoid_mult

(* Instantiation of quantales *)

sublocale near_quantale_Inf \<subseteq> Inf!: near_quantale Inf "op \<cdot>"
  where "abs_complete_lattice.join Inf = op \<sqinter>"
    and "abs_complete_lattice.less_eq Inf = op \<ge>"
    and "abs_complete_lattice.less Inf = op >"
    and "abs_complete_lattice.Meet Inf = Sup"
    and "abs_complete_lattice.meet Inf = op +"
    and "abs_complete_lattice.top Inf = \<bottom>"
    and "abs_complete_lattice.bot Inf = \<top>"
  apply (unfold_locales, auto)
  by (metis qInf_distr Inf_image_eq)

sublocale near_quantale_Inf_unital \<subseteq> Inf!: near_quantale_unital Inf "op \<cdot>" one 
  where "abs_complete_lattice.join Inf = op \<sqinter>"
    and "abs_complete_lattice.less_eq Inf = op \<ge>"
    and "abs_complete_lattice.less Inf = op >"
    and "abs_complete_lattice.Meet Inf = Sup"
    and "abs_complete_lattice.meet Inf = op +"
    and "abs_complete_lattice.top Inf = \<bottom>"
    and "abs_complete_lattice.bot Inf = \<top>"
  by unfold_locales auto

sublocale pre_quantale_Inf \<subseteq> Inf!: pre_quantale Inf "op \<cdot>"
  where "abs_complete_lattice.join Inf = op \<sqinter>"
    and "abs_complete_lattice.less_eq Inf = op \<ge>"
    and "abs_complete_lattice.less Inf = op >"
    and "abs_complete_lattice.Meet Inf = Sup"
    and "abs_complete_lattice.meet Inf = op +"
    and "abs_complete_lattice.top Inf = \<bottom>"
    and "abs_complete_lattice.bot Inf = \<top>"
  apply unfold_locales
  apply (auto intro: Inf_eqI Inf_greatest)
  by (metis Inf.less_eq_def qInf_subdistl Inf_image_eq)

sublocale quantale_Inf \<subseteq> Inf!: quantale Inf "op \<cdot>"
  where "abs_complete_lattice.join Inf = op \<sqinter>"
    and "abs_complete_lattice.less_eq Inf = op \<ge>"
    and "abs_complete_lattice.less Inf = op >"
    and "abs_complete_lattice.Meet Inf = Sup"
    and "abs_complete_lattice.meet Inf = op +"
    and "abs_complete_lattice.top Inf = \<bottom>"
    and "abs_complete_lattice.bot Inf = \<top>"
  apply unfold_locales
  apply (auto intro: Inf_eqI Inf_greatest)
  by (metis inf.orderE qInf_supdistl Inf_image_eq)

sublocale quantale_Inf_unital \<subseteq> Sup!: quantale_unital Inf "op \<cdot>" one
  where "abs_complete_lattice.join Inf = op \<sqinter>"
    and "abs_complete_lattice.less_eq Inf = op \<ge>"
    and "abs_complete_lattice.less Inf = op >"
    and "abs_complete_lattice.Meet Inf = Sup"
    and "abs_complete_lattice.meet Inf = op +"
    and "abs_complete_lattice.top Inf = \<bottom>"
    and "abs_complete_lattice.bot Inf = \<top>"
  by unfold_locales auto

end
