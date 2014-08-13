theory KAD
  imports BBI "$AFP/Kleene_Algebra/Kleene_Algebra"
begin

no_notation 
  sup (infixl "+" 65)

notation sup (infixl "\<squnion>" 65)
  and inf (infixl "\<sqinter>" 70)
  and bot ("\<bottom>")
  and top ("\<top>")

locale embedded_boolean_semiring =
  fixes bool_hom :: "'a :: boolean_algebra \<Rightarrow> 'b :: dioid_one_zero" ("`_" [999] 1000)
  assumes order_hom [iff]: "`p \<le> `q \<longleftrightarrow> p \<le> q"
  and sup_hom [iff]: "`(p \<squnion> q) = `p + `q"
  and inf_hom [iff]: "`(p \<sqinter> q) = `p \<cdot> `q"
  and top_hom [iff]: "`\<top> = 1"
  and bot_hom [iff]: "`\<bottom> = 0"
begin

abbreviation complementation :: "'a \<Rightarrow> 'b" ("!_" [999] 1000) where "!p \<equiv> `(-p)"

lemma mult_idem [simp]: "`p \<cdot> `p = `p"
  by (metis inf_hom inf_idem)

lemma compl_mult_zero [simp]: "!p \<cdot> `p = 0"
  by (metis bot_hom compl_inf_bot inf_hom)

lemma compl_add_one [simp]: "!p + `p = 1"
  by (metis compl_sup_top sup_hom top_hom)

lemma mult_compl_zero [simp]: "`p \<cdot> !p = 0"
  by (metis bot_hom inf_compl_bot inf_hom)

lemma add_compl_one [simp]: "`p + !p = 1"
  by (metis add_comm compl_add_one)

lemma mult_commute_hom: "`p \<cdot> `q = `q \<cdot> `p"
  by (metis inf_commute inf_hom)

lemma compl_eq_compl_iff_hom [simp]: "!x = !y \<longleftrightarrow> x = y"
  by (metis compl_le_compl_iff eq_iff order_hom)

lemma compl_bot_one [simp]: "!\<bottom> = 1"
  by (metis compl_bot_eq top_hom)

lemma compl_top_zero [simp]: "!\<top> = 0"
  by (metis bot_hom compl_top_eq)

lemma compl_inf_add [simp]: "!(x \<sqinter> y) = !x + !y"
  by (metis compl_inf sup_hom)

lemma compl_sup_mult [simp]: "!(x \<squnion> y) = !x \<cdot> !y"
  by (metis compl_sup inf_hom)

lemma compl_iso: "x \<le> y \<Longrightarrow> !y \<le> !x"
  by (metis compl_mono order_hom)

lemma bool_greatest [simp]: "`p \<le> 1"
  by (metis order_hom top_greatest top_hom)

lemma bool_mult_left: "`p\<cdot>x \<le> x"
  by (metis bool_greatest mult_isor mult_onel)

lemma bool_mult_right: "x\<cdot>`p \<le> x"
  by (metis bool_greatest mult_isol mult_oner)

lemma bool_semiring1: assumes "`p\<cdot>x \<le> x\<cdot>`q" shows "x\<cdot>!q \<le> !p\<cdot>x"
proof -
  have "x\<cdot>!q = (`p + !p)\<cdot>x\<cdot>!q" 
    by simp
  also have "... \<le> x\<cdot>(`q\<cdot>!q) + !p\<cdot>x\<cdot>!q" 
    by (metis distrib_right' add_iso assms mult_isor mult_assoc)
  also have "... \<le> !p\<cdot>x" 
    by (metis add_zero_l annir mult_compl_zero bool_mult_right)
  finally show ?thesis .
qed

lemma bool_semiring2: "x\<cdot>!q \<le> !p\<cdot>x \<Longrightarrow> `p\<cdot>x\<cdot>!q \<le> 0"
  apply (subgoal_tac "`p\<cdot>x\<cdot>!q \<le> `p\<cdot>!p\<cdot>x")
  by (metis annil mult_compl_zero, metis mult_isol mult_assoc)

lemma bool_semiring3: "`p\<cdot>x\<cdot>!q \<le> 0 \<Longrightarrow> `p\<cdot>x = `p\<cdot>x\<cdot>`q"
  apply (subgoal_tac "`p\<cdot>x = `p\<cdot>x\<cdot>(`q + !q)")
  by (metis distrib_left add_zeror zero_unique, simp)

lemma bool_semiring4: "`p\<cdot>x = `p\<cdot>x\<cdot>`q \<Longrightarrow> `p\<cdot>x \<le> x\<cdot>`q"
  by (metis bool_mult_left mult_isor)

lemma bool_semiring_eq: "`p\<cdot>x \<le> x\<cdot>`q \<longleftrightarrow> x\<cdot>!q \<le> !p\<cdot>x"
  by (metis bool_semiring1 bool_semiring2 bool_semiring3 bool_semiring4)

end

locale domain_semiring = embedded_boolean_semiring bbi_hom 
  for bbi_hom :: "'a :: bbi \<Rightarrow> 'b :: dioid_one_zero" ("`_" [999] 1000) + 
  fixes domain :: "'b :: dioid_one_zero \<Rightarrow> 'a :: bbi" ("d _" [999] 1000)
  assumes llp: "d x \<le> p \<longleftrightarrow> x \<le> `p\<cdot>x"
begin

abbreviation compl_bbi :: "'a \<Rightarrow> 'b" ("!_" [999] 1000) where "!p \<equiv> `(-p)"

lemma d_zero [simp]: "d 0 = \<bottom>"
  by (metis bot.extremum_unique llp zero_least)

lemma d_one [simp]: "d 1 = \<top>"
  by (metis llp mult_onel mult_oner order_class.order.antisym order_hom top_greatest top_hom)

lemma gla: "d x \<le> p \<longleftrightarrow> !p\<cdot>x \<le> 0"
  by (metis (hide_lams, no_types) annir bool_semiring_eq bot_hom compl_bot_eq llp double_compl mult_oner top_hom)

lemma d_strict: "d x \<le> \<bottom> \<longleftrightarrow> x \<le> 0"
  by (metis annil llp bot_hom)

lemma d_add: "d(x + y) = d x \<squnion> d y"
proof -
  have "\<forall>p. d(x + y) \<le> p \<longleftrightarrow> !p\<cdot>(x + y) \<le> 0"
    by (metis gla)
  hence "\<forall>p. d(x + y) \<le> p \<longleftrightarrow> d x \<squnion> d y \<le> p"
    by (metis distrib_left add_lub gla sup.bounded_iff)
  thus ?thesis
    by (metis eq_iff)
qed

lemma d_iso: "x \<le> y \<Longrightarrow> d x \<le> d y"
  by (metis dual_order.refl gla mult_isol order.trans)

lemma d_greater: "p \<le> d `p"
  by (metis bool_mult_right llp order_hom order_refl order_trans)

lemma d_identity [simp]: "d `p = p"
  by (metis d_greater double_compl gla mult_compl_zero sup_absorb1 sup_commute zero_least)

lemma d_involution [simp]: "d `d x = d x"
  by (metis d_identity)

lemma left_inv [simp]: "`d x\<cdot>x = x"
  by (metis bool_mult_left eq_iff llp)

lemma d_least: "d(`p\<cdot>x) \<le> p"
  by (simp add: llp mult_assoc[symmetric])

lemma imp_exp_law: "d (`p\<cdot>x) = p \<sqinter> d x"
proof -
  have lhs: "d (`p\<cdot>x) \<le> p \<sqinter> d x"
    by (metis bool_mult_left d_iso inf.bounded_iff d_least inf.bounded_iff)
  have "p \<sqinter> d x = p \<sqinter> d(`p\<cdot>x) \<squnion> p \<sqinter> d(!p\<cdot>x)"
    by (metis d_add distrib_right' mult_onel sup_compl_top sup_hom top_hom inf_sup_distrib1)
  also have "... \<le> p \<sqinter> d(`p\<cdot>x)"
    by (metis d_least eq_iff inf_mono sup_mono inf_compl_bot sup_bot.right_neutral)
  finally have rhs: "p \<sqinter> d x \<le> d(`p\<cdot>x)"
    by (metis inf.bounded_iff)
  thus ?thesis
    by (metis antisym lhs)
qed

lemma subloc: "d(x\<cdot>y) \<le> d(x\<cdot>`d y)"
proof (subst llp)
  have "x\<cdot>y \<le> x\<cdot>`d y\<cdot>y"
    by (metis mult_assoc left_inv order_refl)
  also have "... \<le> `d(x\<cdot>`d y)\<cdot>x\<cdot>`d y\<cdot>y"
    by (metis mult_assoc left_inv order_refl)
  also have "... \<le> `d(x\<cdot>`d y)\<cdot>x\<cdot>y"
    by (metis bool_mult_right mult_isor)
  finally show "x\<cdot>y \<le> `d(x\<cdot>`d y)\<cdot>(x\<cdot>y)"
    by (metis mult_assoc)
qed

lemma loc: "d(x\<cdot>y) = d(x\<cdot>`(d y))"
  nitpick oops (*
  by (metis d_identity d_order_preserving eq_iff) *)

lemma d_compl [iff]: "- d `p = d !p"
  by (metis d_identity)

lemma d_fixpoint: "(\<exists>y. x = `d y) \<longleftrightarrow> x = `d x"
  by (metis d_involution)

lemma type_conv: "(\<forall>x. x = `d x \<longrightarrow> P x) \<longleftrightarrow> (\<forall>x. P (`d x))"
  by (metis d_fixpoint)

lemma d_mult_le: "d(x\<cdot>y) \<le> d(x)"
  by (metis bool_mult_right d_iso dual_order.trans subloc)

lemma d_subid: "x \<le> 1 \<Longrightarrow> x \<le> `d(x)"
  by (metis left_inv monoid_mult_class.mult.right_neutral mult_isol)

lemma d_very_strict: "d(x) = \<bottom> \<longleftrightarrow> x = 0"
  by (metis annil bot_hom d_zero left_inv)

lemma d_exp: "`d(`d(x)\<cdot>y) = `d(x) \<cdot> `d(y)"
  by (metis imp_exp_law inf_hom)

lemma d_add_closed: "`d(`d(x) + `d(y)) = `d(x) + `d(y)"
  by (metis d_add d_identity sup_hom)

lemma d_mult_closed: "`d(`d(x)\<cdot>`d(y)) = `d(x) \<cdot> `d(y)"
  by (metis d_identity imp_exp_law inf_hom)

lemma d_glb: "`d(x) \<le> `d(y)\<cdot>`d(z) \<longleftrightarrow> (d(x) \<le> d(y) \<and> d(x) \<le> d(z))"
  by (metis inf.bounded_iff inf_hom order_hom)

lemma d_absorption1 [simp]: "`d(x)\<cdot>(`d(x) + `d(y)) = `d(x)"
  by (metis antisym_conv bool_mult_right d_add_closed mult_idem subdistl)

lemma d_absorption2 [simp]: "`d(x) + `d(x)\<cdot>`d(y) = `d(x)"
  by (metis (hide_lams, no_types) add_comm compl_inf_add compl_le_compl_iff double_compl inf.cobounded1 inf_absorb2 inf_hom)

lemma d_distrib [simp] : "(`d(x) + `d(y))\<cdot>(`d(x) + `d(z)) = `d(x) + `d(y)\<cdot>`d(z)"
  by (metis inf_hom sup_hom sup_inf_distrib1)

definition antidomain :: "'b \<Rightarrow> 'a" ("a _" [999] 1000) where "a x \<equiv> - d(x)"

lemma a_d_compl_d[simp]: "d!d x = a x"
  by (metis antidomain_def d_identity)

lemma a_mult_zero[simp]: "`a x \<cdot> x = 0"
  by (metis antidomain_def d_greater d_identity gla zero_unique)

lemma double_a[simp]: "a `(a x) = d x"
  by (metis antidomain_def d_identity double_compl)

lemma a_gla: "`a(x)\<cdot>y = 0 \<longleftrightarrow> a(x) \<le> a(y)"
  by (metis antidomain_def compl_le_compl_iff gla zero_unique)

lemma a_subdist: "a(x + y) \<le> a(x)"
  by (metis add_ub1 antidomain_def compl_iso d_iso order_hom)

lemma a_1: "`a(x) = 1 \<Longrightarrow> x = 0"
  by (metis a_mult_zero mult_onel)

lemma a_3 [simp]: "`a(x)\<cdot>`a(y)\<cdot>`d(x + y) = 0"
  by (metis a_d_compl_d compl_mult_zero compl_sup_mult d_add d_compl d_involution)

lemma a_add: "`a(x)\<cdot>`a(y) = `a(x + y)"
  by (metis antidomain_def compl_sup d_add inf_hom)

lemma a_export: "a(`a(x)\<cdot>y) = d(x) \<squnion> a(y)"
  by (metis antidomain_def compl_inf double_compl imp_exp_law)

lemma a_zero [simp]: "a(0) = \<top>"
  by (metis antidomain_def compl_bot_eq d_zero)

lemma a_one [simp]: "a(1) = \<bottom>"
  by (metis antidomain_def compl_top_eq d_one)

lemma a_comp_1 [simp]: "`d(x)\<cdot>`a(x) = 0"
  by (metis a_mult_zero double_a)

lemma a_comp_2 [simp]: "`a(x)\<cdot>`d(x) = 0"
  by (metis a_comp_1 mult_commute_hom)

definition fdiamond :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" ("| _ \<rangle> _" [50, 90] 999) where
  "|x\<rangle>y = d(x\<cdot>`y)"

lemma fdia_simp [simp]: "|x\<rangle>(d `p) = |x\<rangle>p"
 by (metis d_identity)

lemma fdia_simp2 [simp]: "d `|x\<rangle>p = |x\<rangle>p"
  by (metis d_identity)

lemma fdia_sup: "|x\<rangle> (p \<squnion> q) = |x\<rangle>p \<squnion> |x\<rangle>q"
  by (metis fdiamond_def sup_hom distrib_left d_add)

lemma fdia_add: "|x + y\<rangle> p = |x\<rangle>p \<squnion> |y\<rangle>p"
  by (metis d_add distrib_right' fdiamond_def)

lemma fdia_mult: "|x\<cdot>y\<rangle> p \<le> |x\<rangle> |y\<rangle> p"
  by (metis fdiamond_def subloc mult_assoc) 

lemma fdia_one: "|1\<rangle>p = p"
  by (metis d_identity fdiamond_def monoid_mult_class.mult.left_neutral)

lemma fdia_zero: "|x\<rangle>\<bottom> = \<bottom>"
  by (metis annir bot_hom d_zero fdiamond_def)

lemma fdia_bool: "|(`p)\<rangle>q = p \<sqinter> q"
  by (metis d_identity fdiamond_def inf_hom)

lemma fdemodalisation1: "q \<sqinter> |x\<rangle>p = \<bottom> \<longleftrightarrow> `q\<cdot>x\<cdot>`p = 0"
  oops (*
  by (metis d_very_strict fdia_bool fdia_mult fdiamond_def) *)

lemma fdemodalisation2: "|x\<rangle>p \<le> q \<longleftrightarrow> !q\<cdot>x\<cdot>`p = 0"
  oops (*
  by (metis d_very_strict fdia_mult fdiamond_def gla loc zero_unique) *)

lemma fdemodalisation3: "|x\<rangle>p \<le> q \<longleftrightarrow> x\<cdot>`p \<le> `q\<cdot>x"
  oops (*
  by (metis d_iso d_mult_le d_order_preserving fdiamond_def imp_exp_law inf.bounded_iff) *)

lemma fdia_iso: "p \<le> q \<Longrightarrow> |x\<rangle>p \<le> |x\<rangle>q"
  by (metis fdia_sup le_iff_sup)

lemma fdia_iso_var: "x \<le> y \<Longrightarrow> |x\<rangle>p \<le> |y\<rangle>p"
  by (metis d_iso fdiamond_def mult_isor)

lemma fdia_zero_var: "|0\<rangle>x = \<bottom>"
  by (metis bot_hom fdia_bool inf_bot_left)

lemma fdia_subdist_1: "|x\<rangle>p \<le> |x\<rangle>(p \<squnion> q)"
  by (metis fdia_iso sup.cobounded1)

lemma fdia_subdist_2: "|x\<rangle>(p \<sqinter> q) \<le> |x\<rangle>p"
  by (metis fdia_iso inf.cobounded1)

lemma fdia_subdist: "|x\<rangle>(p \<sqinter> q) \<le> |x\<rangle>p \<sqinter> |x\<rangle>q"
  by (metis fdia_subdist_2 inf.bounded_iff inf_commute)

lemma dia_diff_var: "|x\<rangle>p \<le> |x\<rangle>(p \<sqinter> -q) \<squnion> |x\<rangle>q"
  by (metis add_compl_one fdia_iso fdia_sup inf.bounded_iff order_hom sup.cobounded2 sup_commute sup_hom sup_inf_distrib1)

lemma fdia_export_1:  "q \<sqinter> |x\<rangle>p = |(`q\<cdot>x)\<rangle>p"
  oops (*
  by (metis fdia_bool fdia_mult) *)

lemma fdia_export_2: "-q \<sqinter> |x\<rangle>p = |!q\<cdot>x\<rangle>p"
  oops (*
  by (metis fdia_export_1) *)

lemma fdia_split: "|x\<rangle>p = (q \<sqinter> |x\<rangle>p) \<squnion> (-q \<sqinter> |x\<rangle>p)"
  by (metis compl_sup_top inf_sup_distrib2 inf_top.left_neutral sup_commute)

lemma a_compl [simp]: "`a(`p) = !p"
  by (metis antidomain_def d_identity)

definition fbox :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" ("| _ ] _" [50, 90] 999) where
  "|x]p \<equiv> a(x\<cdot>!p)"

lemma fbox_fdia: "|x]p = -|x\<rangle>(-p)"
  by (metis antidomain_def fbox_def fdiamond_def)

lemma fdia_fbox: "|x\<rangle>p = -|x](-p)"
  by (metis double_compl fbox_fdia)

lemma fbox_fdia_de_morgan_1: "-|x]p = |x\<rangle>(-p)"
  by (metis double_compl fbox_fdia)

lemma fdia_fbox_de_morgan_2: "-|x\<rangle>p = |x](-p)"
  by (metis double_compl fdia_fbox)

lemma fbox_simp: "|x]p = |x]d(`p)"
  by (metis d_identity)

lemma fbox_simp_2:  "|x]p = d( `|x]p )"
  by (metis d_identity)

lemma fbox_dom: "a(x) = |x]\<bottom>"
  by (metis compl_bot_one fbox_def mult_oner)

lemma fbox_add1: "|x](p \<sqinter> q) = |x]p \<sqinter> |x]q"
  by (metis a_add antidomain_def compl_inf_add d_add d_identity fbox_fdia fdia_sup fdiamond_def inf_hom)

lemma fbox_add2: "|x + y]p = |x]p \<sqinter> |y]p"
  by (metis compl_sup fbox_fdia fdia_add)

lemma fbox_mult: "|x]|y]p \<le> |x\<cdot>y]p"
  by (metis compl_le_compl_iff fbox_fdia fdia_fbox_de_morgan_2 fdia_mult)

lemma fbox_one: "|1]p = p"
  by (metis double_compl fbox_fdia fdia_one)

lemma fbox_one_1: "|x]\<top> = \<top>"
  by (metis compl_bot_eq compl_top_eq fbox_fdia fdia_zero)

lemma fbox_export_1: "-p \<squnion> |x]q = |(`p\<cdot>x)]q"
  by (metis compl_inf fbox_fdia fdia_bool fdia_mult)

lemma fbox_export_2: "p \<squnion> |x]q = |!p\<cdot>x]q"
  by (metis compl_sup double_compl fbox_fdia fdia_bool fdia_mult)

lemma fbox_test: "|(`p)]q = -p \<squnion> q"
  by (metis fbox_export_1 fbox_mult fbox_one)

lemma fbox_test_var: "-p \<sqinter> |!p](-q) = -p \<sqinter> -q"
  by (metis (hide_lams, no_types) compl_sup double_compl fbox_fdia fdia_bool inf_top.right_neutral sup_compl_top sup_inf_distrib1)

lemma fbox_demodalisation3: "p \<le> |x]q \<longleftrightarrow> `p\<cdot>x \<le> x\<cdot>`q"
  by (metis bool_semiring_eq compl_le_compl_iff fbox_fdia_de_morgan_1 fdemodalisation3)

lemma fbox_iso: "p \<le> q \<Longrightarrow> |x]p \<le> |x]q"
  by (metis fbox_add1 inf.orderI inf_absorb1)

lemma fbox_antitone_var: "x \<le> y \<Longrightarrow> |y]p \<le> |x]p"
  by (metis compl_iso fbox_fdia fdia_iso_var order_hom)

lemma fbox_subdist_1: "|x](p \<sqinter> q) \<le> |x]p"
  by (metis fbox_iso inf.cobounded1)

lemma fbox_subdist_2: "|x]p \<le> |x](p \<squnion> q)"
  by (metis fbox_iso sup.cobounded1)

lemma fbox_subdist: "|x]p \<squnion> |x]q \<le> |x](p \<squnion> q)"
  by (metis fbox_subdist_2 sup.bounded_iff sup_commute)


lemma fbox_diff_var: "|x](p \<squnion> -q) \<sqinter> |x]q \<le> |x]p"
  by (metis (hide_lams, no_types) fbox_add1 inf.bounded_iff inf_commute inf_compl_bot inf_sup_distrib2 order_refl sup_bot.left_neutral sup_commute)

lemma fbox_diff: "|x](p \<squnion> -q) \<le> |x]p \<squnion> -|x]q"
  oops

end

locale kad = domain_semiring bbi_hom domain
  for bbi_hom :: "'a :: bbi \<Rightarrow> 'b :: kleene_algebra" ("`_" [999] 1000)
  and domain :: "'b :: kleene_algebra \<Rightarrow> 'a :: bbi" ("d _" [999] 1000)
begin

lemma a_star: "a(x\<^sup>\<star>) = \<bottom>"
  by (metis a_one a_subdist bot.extremum_uniqueI star_plus_one)

lemma d_star: "d(x\<^sup>\<star>) = \<top>"
  by (metis a_star a_zero bot_hom double_a)

lemma fdia_star_unfold: "|1\<rangle>p \<squnion> |x\<rangle>|x\<^sup>\<star>\<rangle>p = |x\<^sup>\<star>\<rangle>p"
  by (metis fdia_add fdia_mult star_unfoldl_eq)

lemma fbox_star_unfold: "|1]p \<sqinter> |x]|x\<^sup>\<star>]p = |x\<^sup>\<star>]p"
  by (metis fbox_add2 fbox_mult star_unfoldl_eq)

lemma fdia_star_unfold_var: "p \<squnion> |x\<rangle>|x\<^sup>\<star>\<rangle>p = |x\<^sup>\<star>\<rangle>p"
  by (metis fdia_one fdia_star_unfold)

lemma fbox_star_unfold_var: "p \<sqinter> |x]|x\<^sup>\<star>]p = |x\<^sup>\<star>]p"
  by (metis fbox_one fbox_star_unfold)

lemma fdia_star_unfoldr: "|1\<rangle>p \<squnion> |x\<^sup>\<star>\<rangle>|x\<rangle>p = |x\<^sup>\<star>\<rangle>p"
  by (metis fdia_add fdia_mult star_unfoldr_eq)

lemma fbox_star_unfoldr: "|1]p \<sqinter> |x\<^sup>\<star>]|x]p = |x\<^sup>\<star>]p"
  by (metis fbox_add2 fbox_mult star_unfoldr_eq)

lemma fdia_star_unfoldr_var: "p \<squnion> |x\<^sup>\<star>\<rangle>|x\<rangle>p = |x\<^sup>\<star>\<rangle>p"
  by (metis fdia_one fdia_star_unfoldr)

lemma fbox_star_unfoldr_var: "p \<sqinter> |x\<^sup>\<star>]|x]p = |x\<^sup>\<star>]p"
  by (metis fbox_one fbox_star_unfoldr)

lemma fdia_star_induct_var: "|x\<rangle>p \<le> p \<Longrightarrow> |x\<^sup>\<star>\<rangle>p \<le> p"
  by (metis fdemodalisation3 star_sim1)

lemma fbox_star_induct_var: "p \<le> |x]p \<Longrightarrow> p \<le> |x\<^sup>\<star>]p"
  by (metis fbox_demodalisation3 star_sim2)

lemma fdia_star_induct: "q \<squnion> |x\<rangle>p \<le> p \<Longrightarrow> |x\<^sup>\<star>\<rangle>q \<le> p"
  by (metis (hide_lams, no_types) fdia_star_induct_var fdia_subdist_2 inf_sup_aci(1) le_iff_inf le_iff_sup sup.bounded_iff)

lemma fbox_star_induct: "p \<le> q \<sqinter> |x]p \<Longrightarrow>  p \<le> |x\<^sup>\<star>]q"
proof -
  assume a1: "p \<le> q \<sqinter> | x ] p"
  have "\<And>u v y. (u\<Colon>'a) \<le> v \<and> u \<le> y \<longrightarrow> u \<squnion> v \<sqinter> y = v \<sqinter> y"
    by (metis inf.bounded_iff inf_sup_aci(5) sup.order_iff)
  hence "\<And>u w. u \<sqinter> | w ] u = u"
    by (metis d_one d_order_preserving fbox_antitone_var fbox_one inf_top.left_neutral sup.order_iff sup_inf_absorb)
  thus "p \<le> | x\<^sup>\<star> ] q"
    using a1 by (metis inf.bounded_iff)
qed

lemma fdia_star_induct_eq: "q \<squnion> |x\<rangle>p = p \<Longrightarrow> |x\<^sup>\<star>\<rangle>q \<le> p"
  by (metis fdia_star_induct order_refl)

lemma fbox_star_induct_eq: "q \<sqinter> |x]p = p \<Longrightarrow> p \<le> |x\<^sup>\<star>]q"
  by (metis d_greater d_identity fbox_star_induct)

end

locale local_domain_semiring = domain_semiring +
  assumes fbox_locality: "|x]p * q \<le> |x](p * q)"
begin

lemma fbox_frame: "p \<le> |x]q \<Longrightarrow> p * r \<le> |x](q * r)"
  by (metis fbox_locality Sup.qisor Sup.order_trans)

end

locale local_kad = kad + local_domain_semiring
begin

definition ht :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool" ("\<turnstile> _ _ _" [55,0,55] 50) where "\<turnstile> p x q \<longleftrightarrow> p \<le> |x]q"

lemma hl_skip: "p \<le> q \<Longrightarrow> \<turnstile> p 1 q"
  by (metis fbox_one ht_def)

lemma hl_strengthen: "q \<le> q' \<Longrightarrow> \<turnstile> p 1 q \<Longrightarrow> \<turnstile> p 1 q'"
  by (metis fbox_one ht_def inf.boundedE inf_absorb2)

lemma hl_weaken: "p' \<le> p \<Longrightarrow> \<turnstile> p 1 q \<Longrightarrow> \<turnstile> p' 1 q"
  by (metis fbox_one hl_strengthen ht_def)

lemma hl_seq: "\<turnstile> p x r \<Longrightarrow> \<turnstile> r y q \<Longrightarrow> \<turnstile> p x\<cdot>y q"
  by (metis (full_types) fbox_iso fbox_mult ht_def inf.boundedE inf_absorb2)

lemma hl_choice: "\<turnstile> p x q \<Longrightarrow> \<turnstile> p y q \<Longrightarrow> \<turnstile> p x + y q"
  by (metis ht_def inf_greatest fbox_add2)

lemma hl_iteration: "\<turnstile> p x p \<Longrightarrow> \<turnstile> p x\<^sup>\<star> p"
  by (metis fbox_star_induct_var ht_def)

lemma sl_frame: "\<turnstile> p x q \<Longrightarrow> \<turnstile> (p * r) x (q * r)"
  by (metis fbox_frame ht_def)

end


end
