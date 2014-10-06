theory Examples
  imports Hoare GCD
begin

no_notation Set.image (infixr "`" 90)
  and times (infixl "*" 70)

record state =
  x :: nat
  y :: nat
  z :: nat
  w :: nat

(* Assignments *)
lemma "\<turnstile> true (`x := 2) \<lbrace> `x = 2 \<rbrace>"
  by hoare auto

(* Sequential composition *)
lemma swap: 
  "\<turnstile> \<lbrace> `x = xo \<and> `y = yo \<rbrace> (
    `z := `x;
    `x := `y;
    `y := `z
  ) \<lbrace> `x = yo \<and> `y = xo \<rbrace>"
  by hoare auto

(* If statement *)
lemma maximum: "\<turnstile> true (if `x \<ge> `y then `z := `x else `z := `y fi) \<lbrace> `z = max `x `y \<rbrace>"
  by hoare auto

(* While statement *)
lemma euclids:
  "\<turnstile> \<lbrace> `x = xo \<and> `y = yo \<rbrace> (
    while `y \<noteq> 0 
    inv \<lbrace> gcd `x `y = gcd xo yo \<rbrace>
    do
      `z := `y;
      `y := `x mod `y;
      `x := `z
    od
  ) \<lbrace> `x = gcd xo yo \<rbrace>"
  by (hoare, auto) (metis gcd_red_nat)

(* Pointers *)
lemma "\<turnstile> (\<lbrace> `x \<mapsto> `y \<rbrace> * \<lbrace> `z \<mapsto> `w \<rbrace>) skip \<lbrace> `x \<noteq> `z \<rbrace>"
  by hoare (auto simp: sep_conj_def ortho_def is_singleton_def)

lemma "emp * emp \<le> skip emp"
  by (auto simp: emp_def sep_conj_def ortho_def)

lemma "\<lbrace> `x \<mapsto> `y \<rbrace> * \<lbrace> `z \<mapsto> `w \<rbrace> \<le> (`y := `w) \<lbrace> `x \<noteq> `z \<rbrace>"
  by (auto simp: sep_conj_def ortho_def is_singleton_def)

hide_const x y z w
end
