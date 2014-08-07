theory PartialMonoid
  imports Main
begin

section {* Partial monoid *}

no_notation 
  one_class.one ("1") and
  times (infixl "*" 70)

notation bot ("\<bottom>")

text {* Signature of our classes *}

class pmult =
  fixes pmult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 80)

class pmult_defined =
  fixes pmult_defined :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "##" 55)

class pmult_one =
  fixes pmult_one :: "'a" ("1")

text {* Domain theoretical way of defining pmult semigroups, i.e., adding a \<bottom> (seeking) element. *}

class partial_semigroup_bot = pmult + bot +
  assumes pbot_assoc: "(x * y) * z = x * (y * z)"
  and botl [simp]: "x * \<bottom> = \<bottom>"
  and botr [simp]: "\<bottom> * x = \<bottom>"

text {* 
  Let the binary relation ## be: x ## y \<longleftrightarrow> x + y \<noteq> \<bottom>, one can naturally define the
  following class based on the pmult semigroup with bottom element.
*}

class partial_semigroup_var = pmult + pmult_defined +
  assumes pmult_defr: "x ## (y * z) \<Longrightarrow> y ## z"
  and pmult_defl: "(x * y) ## z \<Longrightarrow> x ## y"
  and pmult_def_assoc: "x ## (y * z) = (x * y) ## z"
  and pmult_assoc_var: "x ## (y * z) \<Longrightarrow> (x * y) * z = x * (y * z)"

text {*
  A simpler pmult semigroup can be defined where it states that if x * y and (x * y) * z 
  are defined, then y * z is also defined.
*}

class partial_semigroup = pmult + pmult_defined +
  assumes pmult_def: "(x * y) ## z \<and> x ## y \<longleftrightarrow> x ## (y * z) \<and> y ## z"
  and pmult_assoc: "\<lbrakk>x ## (y * z); x ## y\<rbrakk> \<Longrightarrow> (x * y) * z = x * (y * z)"

class totality = pmult_defined +
  assumes totality[simp]: "x ## y"

class total_semigroup = partial_semigroup + totality
begin

lemma total_assoc: "(x * y) * z = x * (y * z)"
  by (metis pmult_assoc totality)

sublocale semigroup "op *" 
  by default (simp add: total_assoc)

end

text {* 
  As expected, the pmult semigroup with bottom element is the strongest, where one can
  derive the other classes.
*}

sublocale partial_semigroup_bot \<subseteq> partial_semigroup_var "op *" "\<lambda>x y. x * y \<noteq> \<bottom>"
  by (default, metis botl, metis botr, (metis pbot_assoc)+)

sublocale partial_semigroup_var \<subseteq> partial_semigroup
  by default (metis pmult_def_assoc pmult_defl pmult_defr, metis pmult_assoc_var)

sublocale partial_semigroup_bot \<subseteq> partial_semigroup "op *" "\<lambda>x y. x * y \<noteq> \<bottom>" ..

text {*
  We select the weakest pmult semigroup to continue our hierarchy up to commutative monoid.
*}

class partial_ab_semigroup = pmult + pmult_defined +
  assumes pmult_def: "(x * y) ## z \<and> x ## y \<Longrightarrow> x ## (y * z) \<and> y ## z"
  and pmult_assoc: "\<lbrakk>x ## (y * z); x ## y\<rbrakk> \<Longrightarrow> (x * y) * z = x * (y * z)"
  and pmult_comm_def: "x ## y \<Longrightarrow> y ## x"
  and pmult_comm: "x ## y \<Longrightarrow> x * y = y * x"
begin

lemma "x ## y = y ## x"
  by (metis pmult_comm_def)

lemma pmult_def_eq: "(x * y) ## z \<and> x ## y \<longleftrightarrow> x ## (y * z) \<and> y ## z"
  by (metis pmult_comm_def pmult_def)

subclass partial_semigroup 
  by default (metis pmult_def_eq, metis pmult_assoc)

end

class total_ab_semigroup = partial_ab_semigroup + totality
begin

lemma total_assoc: "(x * y) * z = x * (y * z)"
  by (metis pmult_assoc totality)

lemma total_comm: "x * y = y * x"
  by (metis pmult_comm totality)

subclass total_semigroup ..

end

class partial_monoid = partial_semigroup + pmult_one + 
  assumes pmult_one_defr [simp]: "x ## 1"
  and pmult_one_defl [simp]: "1 ## x"
  and pmult_oner: "x * 1 = x"
  and pmult_onel: "1 * x = x"

class total_monoid = partial_monoid + totality
begin
subclass total_semigroup ..

sublocale monoid "op *" 1
  by default (simp_all add: pmult_oner pmult_onel)

end

class partial_comm_monoid = partial_ab_semigroup + pmult_one +
  assumes pone_defr: "x ## 1"
  and poner: "x * 1 = x"
begin

subclass partial_monoid
  by default (auto simp: pone_defr poner pmult_comm pmult_comm_def)

end

class total_comm_monoid = partial_comm_monoid + totality
begin
subclass total_ab_semigroup ..
subclass total_monoid ..

sublocale comm_monoid "op *" 1
  by default (simp_all add: total_comm)
end

section {* Models of partial monoids *}

text {* 
  The natural model of a partial monoid is partial functions. 
*}

typedef ('a, 'b) pfun = "UNIV :: ('a \<Rightarrow> 'b option) set" ..
setup_lifting type_definition_pfun

instantiation pfun :: (type, type) partial_semigroup
begin
lift_definition pmult_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" is map_add .
lift_definition pmult_defined_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" is "\<lambda>x y. dom x \<inter> dom y = {}" .
instance 
  by default (transfer, fastforce)+
end

instantiation pfun :: (type, type) partial_monoid
begin
lift_definition pmult_one_pfun :: "('a, 'b) pfun" is empty .
instance
  by default (transfer, fastforce)+
end

text {*
  We can also have a model where we add a new bottom element.
*}

typedef ('a, 'b) pfun_bot = "UNIV :: ('a \<Rightarrow> ('b option) option) set" ..
setup_lifting type_definition_pfun_bot

instantiation pfun_bot :: (type, type) partial_semigroup_bot
begin
lift_definition bot_pfun_bot :: "('a, 'b) pfun_bot" is "\<lambda>x. Some None" .
lift_definition pmult_pfun_bot :: "('a, 'b) pfun_bot \<Rightarrow> ('a, 'b) pfun_bot \<Rightarrow> ('a, 'b) pfun_bot" 
  is "\<lambda>x y. if dom x \<inter> dom y = {} then map_add x y else (\<lambda>x. Some None)" .
instance
  by default (transfer, fastforce)+
end

text {*
  And obviously, it is also a model for our weaker semigroup.
*}

instantiation pfun_bot :: (type, type) partial_semigroup
begin
lift_definition pmult_defined_pfun_bot :: "('a, 'b) pfun_bot \<Rightarrow> ('a, 'b) pfun_bot \<Rightarrow> bool" is
  "\<lambda>x y. dom x \<inter> dom y = {}" .
instance
  by default (transfer, auto)+
end

text {*
  We could instantiate the heap as a partial function from nat to nat
*}
(*type_synonym heap = "(nat, nat) pfun"*)


end
