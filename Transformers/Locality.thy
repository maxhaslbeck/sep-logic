theory Locality
  imports Sets PredicateTransformers
begin

no_notation 
  one_class.one ("1") and
  times (infixl "*" 70)

notation pmult (infixl "*" 80)

section {* Locality *}

text {* 
  Calcagno and O'Hearn define locality as state transformers f where \<forall>x y. f(x * y) \<le> f x * {y}
*}

definition local_stran :: "('a :: partial_semigroup \<Rightarrow> 'a set) \<Rightarrow> bool" where
  "local_stran f \<equiv> \<forall>x y. f(x * y) \<le> f x * {y}"

text {*
  The Hoare triple can be defined in terms of state transformers
*}

definition ht_stran :: "'a set \<Rightarrow> ('a :: partial_semigroup \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> bool" ("\<turnstile> \<guillemotleft>_\<guillemotright> _ \<guillemotleft>_\<guillemotright>") where
  "\<turnstile> \<guillemotleft>p\<guillemotright> f \<guillemotleft>q\<guillemotright> \<equiv> \<forall>x \<in> p. f x \<le> q"

text {*
  Locality suffices to prove the frame rule
*}

lemma frame_sl_stran: "\<lbrakk>local_stran f; \<turnstile> \<guillemotleft>p\<guillemotright> f \<guillemotleft>q\<guillemotright>\<rbrakk> \<Longrightarrow> \<turnstile> \<guillemotleft>p * r\<guillemotright> f \<guillemotleft>q * r\<guillemotright>"
proof (simp add: ht_stran_def, default)
  fix x :: 'a assume assms: "local_stran f" "\<forall>x \<in> p. f x \<le> q" "x \<in> p * r"
  then obtain y z where yz: "x = y * z \<and> y \<in> p \<and> z \<in> r"
    by (auto simp add: pmult_set_def)
  have "f (y * z) \<le> f y * {z}"
    by (metis assms(1) local_stran_def)
  also have "... \<le> f y * r"
    by (metis Sup_pmult.Sup.qisol empty_subsetI insert_subset yz)
  also have "... \<le> q * r"
    by (metis Sup_pmult.Sup.qisor assms(2) yz)
  finally show "f x \<subseteq> q * r"
    by (metis yz)
qed

text {*
  Locality can be defined for predicate transformers
*}

definition local_ptran :: "('a :: partial_semigroup set \<Rightarrow> 'a set) \<Rightarrow> bool" where
  "local_ptran F \<equiv> \<forall>x y. (F x) * y \<le> F (x * y)"

text {*
  Locality for predicate transformers is weaker than the one for state transformers
  Maybe that's why Calgano has a top element?
*}

(* Liftins state transformers to predicate transformers*)
definition ptran :: "('a :: partial_semigroup \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "ptran f \<equiv> \<lambda>Y. {x. f x \<subseteq> Y}" 

lemma [iff]: "y \<in> ptran f X \<longleftrightarrow> f y \<le> X"
  by (auto simp: ptran_def)

lemma local_stran_ptran: "local_stran f \<Longrightarrow> local_ptran (ptran f)"
proof (simp add: local_ptran_def, safe)
  fix x x' X Y
  assume assms: "local_stran f"  "x \<in> ptran f X * Y" "x' \<in> f x"
  then obtain y z :: 'a where yz: "x = y * z \<and> y ## z \<and> f y \<le> X \<and> z \<in> Y"
    by (auto simp: pmult_set_def)
  from assms and this have "f x \<le> (f y) * {z}"
    by (simp add: pmult_set_def local_stran_def)
  also have "... \<le> X * Y" using yz
    by (metis (erased, hide_lams) Sup.order_trans Sup_pmult.Sup.qisol Sup_pmult.Sup.qisor empty_subsetI insert_subset)
  finally show "x' \<in> X * Y" using assms by auto
qed

lemma "local_ptran (ptran f) \<Longrightarrow> local_stran f"
  nitpick oops

text {*
  Locality defined for predicate transforemrs is equivalent to F * id \<le> F
*}

(* It needs to prove that predicate transformers form a partial quantale (which it is obvious) *)

definition local :: "('a :: partial_semigroup \<Rightarrow> 'a set) \<Rightarrow> bool" where
  "local F \<equiv> F \<cdot> id \<le> F"

lemma local_ptran_eq1: "local_ptran F \<Longrightarrow> local F"
proof (simp add: local_def, rule le_funI)
  fix x assume "local_ptran F"
  hence "\<forall>y z. x = y * z \<longrightarrow> (F y) * z \<le> F x"
    by (auto simp: local_ptran_def)
  moreover have "(F * id) x = \<Squnion> {F y * id z | y z. x = y * z}"
    by simp
  ultimately show "(F * id) x \<le> F x"
    by auto
qed

lemma local_ptran_eq2: "local F \<Longrightarrow> local_ptran F"
proof (simp add: local_ptran_def local_def, default, default)
  fix y z assume assms: "F * id \<le> F"
  obtain x :: "'a set" where xyz: "x = y * z" by simp
  have "F y * z \<le> \<Squnion> {F y * z | y z. x = y * z}" using xyz
    by (auto intro: Sup_upper)
  also have "... = (F * id) x"
    by simp
  also have "... \<le> F x"
    by (metis assms le_funD)
  finally show "F y * z \<le> F (y * z)"
    by (metis xyz)
qed

theorem local_ptran_eq: "local_ptran F = local F"
  by (metis local_ptran_eq1 local_ptran_eq2)

lemma local_ptran: "local F \<Longrightarrow> F x * y \<le> F (x * y)"
  by (metis local_ptran_def local_ptran_eq2)

end
