fun antiquote_tr f a =
  let
    fun tr i ((t as Const (c, _)) $ u) =
          if (c = a) then tr i u $ Bound i
          else if c = f then Syntax.const "the" $ (Bound i $ tr i u)
          else tr i t $ tr i u
      | tr i (t $ u) = tr i t $ tr i u
      | tr i (Abs (x, T, t)) = Abs (x, T, tr (i + 1) t)
      | tr _ a = a;
  in tr 0 end;

fun quote2_tr f a t = Abs ("h", dummyT, antiquote_tr f a (Term.incr_boundvars 1 t));

fun quote_tr [t] = Syntax_Trans.quote_tr @{syntax_const "_antiquote_s"} (quote2_tr 
  @{syntax_const "_antiquote_to_h"} @{syntax_const "_antiquote_h"} t)
    | quote_tr ts = raise TERM ("quote_tr", ts)

fun quote_tr' [t] = Syntax.const "split" $ (quote_tr [t])
  | quote_tr' ts = raise TERM ("quote_tr'", ts)

fun if_tr [p, x, y] = Syntax.const "sup" $ 
    (Syntax.const "comp" $ (Syntax.const "lift_pred_predT" $ (quote_tr' [p])) $ x) $
    (Syntax.const "comp" $ (Syntax.const "lift_pred_predT" $ (Syntax.const "uminus" $ (quote_tr' [p]))) $ y)
  | if_tr ts = raise TERM ("if_tr", ts)

fun while_tr [p, x] = Syntax.const "while" $ (quote_tr' [p]) $ x
  | while_tr ts = raise TERM ("while_tr", ts)

fun while_inv_tr [p, i, x] = Syntax.const "While_inv" $ (quote_tr' [p]) $ i $ x
  | while_inv_tr ts = raise TERM ("while_inv_tr", ts)

fun update_name_tr (Free (x, T) :: ts) = list_comb (Free (suffix "_update" x, T), ts)
  | update_name_tr (Const (x, T) :: ts) = list_comb (Const (suffix "_update" x, T), ts)
  | update_name_tr (((c as Const ("_constrain", _)) $ t $ ty) :: ts) =
      if Term_Position.is_position ty then list_comb (c $ update_name_tr [t] $ ty, ts)
      else
        list_comb (c $ update_name_tr [t] $
          (Lexicon.fun_type $
            (Lexicon.fun_type $ Lexicon.dummy_type $ ty) $ Lexicon.dummy_type), ts)
  | update_name_tr ts = raise TERM ("update_name_tr", ts);

fun assign_tr [x, t] = Syntax.const "lift_state_a_predT" $
  quote_tr' [(Syntax.const "_antiquote_s" $ update_name_tr [x, absdummy dummyT t])]
  | assign_tr ts = raise TERM ("assign_tr", ts)

fun mutation_tr [x, t] = Syntax.const "lift_state_heap_predT" $
  quote_tr' [Syntax.const @{syntax_const "_antiquote_h"} $ (Syntax.const "heap_update" $ x $ t)]
  | mutation_tr ts = raise TERM ("mutation_tr", ts)

fun mutation_tr' [x, t] = (Syntax.const "heap_update" $ x $ t)
  | mutation_tr' ts = raise TERM ("mutation_tr", ts)
