(*  Abbey Reese: Code Sample: SATSolver  *)


type var = int (* the number ~1 indicates variable 1 is negated *)

type clause = var list (* a list of OR'd variables: [~1, 2] == ~1 \/ 2 *)

type formula = clause list (* conjunction (i.e. "and") of clauses *)

type assignment = var list

exception Fail of string



(*
 * isEmpty : clause -> (unit -> 'a) -> (unit -> 'a) -> 'a`
 *
 * ENSURES : isEmpty clause sc fc ==>*
 *    runs sc ()     if clause is the empty clause
 *    runs fc ()     otherwise
 *)
fun isEmpty (clause : clause) (sc : unit -> 'a) (fc : unit -> 'a) : 'a =
  case clause of
    [] => sc ()
  | _  => fc ()



(*
 * isSingleton : clause -> (var -> 'a) -> (unit -> 'a) -> 'a
 *
 * ENSURES : isSingleton clause sc fc ==>*
 *    - sc x      if clause contains exactly one variable, x
 *    - fc ()     otherwise
 *)
fun isSingleton (clause : clause) (sc : var -> 'a) (fc : unit -> 'a) : 'a =
  case clause of
    [x] => sc x
  | _   => fc ()

(********************************************************************************)
(* Uninteresting Helpers *)

(*
 * foldr : ('a * 'b -> ('b -> 'c) -> 'c) -> 'b -> 'a list -> ('b -> 'c) -> 'c
 *
 * REQUIRES: g (a,b) k' total when k' is valuable and total and (a,b) is valuable.
 *
 * ENSURES : foldr g z lst k == k (List.foldr (g (fn x => x)) z lst)
 *
 * The idea is that the folding function g calls its own continuation with the
 * the updated accumulator. 
 *)
fun foldr
  (g : 'a * 'b -> ('b -> 'c) -> 'c)
  (z : 'b)
  (lst : 'a list)
  (k : 'b -> 'c)
  : 'c =
    case lst of
      []    => k z
    | x::xs => foldr g z xs (fn b => g (x, b) k)


(*
 * append : 'a list * 'a list -> ('a list -> 'b) -> 'b
 *
 * ENSURES : (lst1 @ lst2) k == k (List.@ (lst1, lst2))
 *)
fun ((lst1 : 'a list) @ (lst2 : 'a list)) (k : 'a list -> 'b) : 'b =
  foldr (fn (x,acc) => fn k => k (x::acc)) lst2 lst1 k
val append = op@

(********************************************************************************)


(*
 * find : ('a -> ('b -> 'c) -> (unit -> 'c) -> 'c)
 *     -> 'a list
 *     -> ('b -> 'c)
 *     -> (unit -> 'c)
 *     -> 'c
 *
 * find an element in the list: lst s.t. the element satisfies p
 * p takes in a element from the list, a success cont. and a failure cont.
 *)
fun find
  (p : 'a -> ('b -> 'c) -> (unit -> 'c) -> 'c)
  (cnf : formula)
  (sc : 'b -> 'c)
  (fc : unit -> 'c)
  : 'c =
    case cnf of
      [] => fc ()
    | x::xs => p x sc (fn () => find p xs sc fc)
                                                           



(*
 * checkVar : var * var -> (unit -> 'a) -> (unit -> 'a) -> (unit -> 'a) -> 'a`
 *
 * ENSURES : checkVar (x,y) same neg diff ==>*
 *    - same ()    if x and y are the same variable
 *    - neg  ()    if x and y are the same variable but one is negated
 *    - diff ()    if x and y are different variables
 *)
fun checkVar 
  (x : var,  y : var)
  (same : unit -> 'a)
  (neg : unit -> 'a) 
  (diff : unit -> 'a)
  : 'a = 
    if x = y then same () else
      if x = ~y then neg () else diff ()

      

(*
 * pickVar : formula -> var option
 *
 * REQUIRES: the input does not contain an empty clause
 *
 * ENSURES : pickVar formula ==>*
 *    - NONE      if no variables exist in formula
 *    - SOME x    where x is some var in formula
 *)
fun pickVar (formula : formula) : var option =
  case formula of
    [] => NONE
  | []::_ => raise Fail "REQUIRES violated"
  | (x::_)::_ => if x < 0 then SOME (~x) else SOME x






(* updateClauseVar : var -> clause -> (unit -> 'a) -> (clause -> 'a) -> 'a
 * ENSURES : updateClauseVar var clause sat update ==>*
 *    - sat ()            if the assignment of var makes the clause satisfied
 *    - update clause     otherwise, where clause' is clause with ~var removed
 *)
fun updateClauseVar (var : var) ([]: clause) (sat : unit -> 'a) (update : clause -> 'a)  : 'a = update []
  | updateClauseVar  var        (x::xs)       sat                update =
    checkVar (var, x) 
    sat                                                           (* if x == var   satisfied ! *)
    (fn () => updateClauseVar var xs sat update)                  (* if x == ~var, x removed *)
    (fn () => updateClauseVar var xs sat (fn L => update(x::L)))  (* if x != var,  x stays *)





(* updateFormulaVar : var -> formula -> (formula -> 'a) -> 'a
 * ENSURES : updateFormulaVar var formula k ==>* k formula'
 *           where formula' is the formula after assigning var
 *)
fun updateFormulaVar (var : var)([] : formula)(k : formula -> 'a) : 'a = k []
  | updateFormulaVar  var       (c1::cs)       k =
    updateClauseVar  var c1 
    (fn () =>  updateFormulaVar var cs k)                        (* if clause is satisfied, remove clause, continue updating formula *)
    (fn c' =>  updateFormulaVar var cs (fn c'' => k(c'::c'')))   (* if not update the clause, continue updating formula *)




(* unitProp : formula -> (assignment * formula -> 'a) -> (unit -> 'a) -> 'a
 *
 * ENSURES : unitProp formula update unsat ==>*
 *    - unsat ()                if through unit propagation, we can derive the
 *                                the empty clause
 *    - update (asgn,formula')  otherwise, where asgn is the variables assigned
 *                                through unit propagation and formula' is
 *                                formula with no more singleton clauses and no
 *                                empty clauses
 *)
fun unitProp (formula : formula) (update : assignment * formula -> 'a) (unsat : unit -> 'a): 'a =
    find (isSingleton) formula
    (* if it finds a singleton this variable must be set to true, update formula and assignment *)
    (fn var => updateFormulaVar var formula (fn f => unitProp f (fn (asgn',f') => update(var::asgn',f')) (unsat)))
    (* otherwise check for an empty clause => unsatisfiability *)
    (fn () => find (isEmpty) formula (unsat) (fn () => update([],formula)))




(* dpll : formula -> (assignment -> 'a) -> (unit -> 'a) -> 'a
 * ENSURES : dpll formula sat unsat ==>*
 *    - unsat ()     if there is no satisfying assignment to formula
 *    - sat asgn     if there is a satisfying assignment to formula, asgn
 *)
fun dpll (cnf : formula)(sat : assignment -> 'a)(unsat : unit -> 'a): 'a =
  unitProp cnf (fn (a,cnf') => 
  case (pickVar cnf') of
    NONE     => sat(a)
   |SOME var => dpll ([var]::cnf')
                     (fn a' => (a' @ a) sat)
                     (fn () => dpll ([~var]::cnf') (fn a' => (a' @ a) sat) (unsat)))
                     (unsat)

