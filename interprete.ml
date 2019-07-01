type ide = string;;
type exp =
  Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp | Modulus of exp * exp |
  Eq of exp * exp | Leq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
  Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp | Letrec of ide * exp * exp |
  ETree of tree | ApplyOver of exp * exp | Update of (ide list) * exp * exp | Select of (ide list) * exp * exp
and tree = Empty | Node of ide * exp * tree * tree;;

(* ambiente polimorfo *)
type 't env = ide -> 't;; (* funzione da stringa a valore *)
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;; (* update dell'ambiente *)

(* tipi esprimibili *)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun | Tree of treeVal
and evFun = ide * exp * evT env
and treeVal = Empty | NodeVal of ide * evT * treeVal * treeVal;; (* albero valutato *)

(* rts *)
(* type checking statico *)
let typecheck (s : ide) (v : evT) : bool =
  match s with
    "int" ->
      (match v with
        Int(_) -> true
      | _ -> false)
  | "bool" ->
      (match v with
        Bool(_) -> true
      | _ -> false)
  | _ -> failwith("not a valid type");;

(* funzioni primitive *)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x, y) with
    (Int(a), Int(b)) -> Int(a * b))
  else failwith("Type error");;
let sum x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x, y) with
    (Int(a), Int(b)) -> Int(a + b))
  else failwith("Type error");;
let diff x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x, y) with
    (Int(a), Int(b)) -> Int(a - b))
  else failwith("Type error");;
let modulus x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x, y) with
    (Int(a), Int(b)) -> Int(a mod b))
  else failwith("Type error");;
let eq x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x, y) with
    (Int(a), Int(b)) -> Bool(a = b))
  else failwith("Type error");;
let leq x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x, y) with
    (Int(a), Int(b)) -> Bool(a <= b))
  else failwith("Type error");;
let minus x = if (typecheck "int" x) 
  then (match x with
    Int(n) -> Int(-n))
  else failwith("Type error");;
let iszero x = if (typecheck "int" x)
  then (match x with
    Int(n) -> Bool(n = 0))
  else failwith("Type error");;
let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x, y) with
    (Bool(a), Bool(b)) -> Bool(a && b))
  else failwith("Type error");;
let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x, y) with
    (Bool(a), Bool(b)) -> (Bool(a || b)))
  else failwith("Type error");;
let non x = if (typecheck "bool" x)
  then (match x with
    Bool(true) -> Bool(false) |
    Bool(false) -> Bool(true))
  else failwith("Type error");;

(* valutatore di espressioni *)
let rec eval (e : exp) (r : evT env) : evT =
  match e with
    Eint n -> Int n
  | Ebool b -> Bool b
  | IsZero a -> iszero (eval a r)
  | Den i -> applyenv r i
  | Eq (a, b) -> eq (eval a r) (eval b r)
  | Leq (a, b) -> leq (eval a r) (eval b r)
  | Prod (a, b) -> prod (eval a r) (eval b r)
  | Sum (a, b) -> sum (eval a r) (eval b r)
  | Diff (a, b) -> diff (eval a r) (eval b r)
  | Modulus (a, b) -> modulus (eval a r) (eval b r)
  | Minus a -> minus (eval a r)
  | And (a, b) -> et (eval a r) (eval b r)
  | Or (a, b) -> vel (eval a r) (eval b r)
  | Not a -> non (eval a r)
  | Ifthenelse (a, b, c) ->
    let g = (eval a r) in
      if (typecheck "bool" g) 
        then (if g = Bool(true) then (eval b r) else (eval c r))
        else failwith "nonboolean guard"
  | Let (i, e1, e2) -> eval e2 (bind r i (eval e1 r))
  | Fun (formPar, fBody) -> FunVal(formPar, fBody, r)
  | FunCall (f, eArg) ->
    let fClosure = (eval f r) in
      (match fClosure with
        FunVal (arg, fBody, fDecEnv) ->
          eval fBody (bind fDecEnv arg (eval eArg r))
      | RecFunVal (f, (arg, fBody, fDecEnv)) ->
          let aVal = (eval eArg r) in
            let rEnv = (bind fDecEnv f fClosure) in
              let aEnv = (bind rEnv arg aVal) in
                eval fBody aEnv
      | _ -> failwith "non functional value")
  | Letrec (f, funDef, letBody) ->
    (match funDef with
      Fun (formPar, fBody) -> let r1 = (bind r f (RecFunVal(f, (formPar, fBody, r)))) in
        eval letBody r1
      | _ -> failwith "non functional def")
  | ETree t -> Tree(evalTree t r) (* valutazione standard *)
  | ApplyOver (f, t) ->
      (match t with
        ETree tree ->
          (match f with
            Fun (_) -> Tree(applyover f tree r)
          | _ -> failwith "Error: function expected")
      | _ -> failwith "Error: ApplyOver needs a tree")
  | Update (path, f, t) ->
      (match t with
        ETree tree ->
          (match f with
            Fun (_) -> Tree(update path f tree r)
          | _ -> failwith "Error: function expected")
      | _ -> failwith "Error: Update needs a tree")
  | Select (path, f, t) ->
      (match t with
        ETree tree ->
          (match f with
            Fun (_) -> Tree(select path f tree r)
          | _ -> failwith "Error: function expected")
      | _ -> failwith "Error: Select needs a tree")

and evalTree (t : tree) (r : evT env) : treeVal =
  match t with
    Empty -> Empty
  | Node (ide, exp, left, right) -> NodeVal (ide, eval exp r, evalTree left r, evalTree right r) (* l'ambiente non cambia *)
  | _ -> failwith "Error: bad tree format"

and applyover f (t : tree) (r : evT env) : treeVal = (* sostituisco la semplice valutazione con la chiamata di funzione *)
  match t with
    Empty -> Empty
  | Node (ide, exp, left, right) -> NodeVal (ide, eval (FunCall(f, exp)) r, applyover f left r, applyover f right r)
  | _ -> failwith "Error: bad tree format"

and update (path : ide list) f (t : tree) (r : evT env) : treeVal =
  match t with
    Empty -> Empty
  | Node (ide, exp, left, right) ->
      (match path with
        [] -> evalTree t r (* nessun cammino, valutazione standard *)
      | head :: [] -> 
          if (head = ide) (* mi trovo nel nodo target? *)
            then NodeVal (ide, eval (FunCall(f, exp)) r, evalTree left r, evalTree right r)
            else evalTree t r (* valutazione standard *)
      | head :: rest ->
        if (head = ide) (* nel caso di più cammini possibili, vengono tutti seguiti *)
          then NodeVal (ide, eval exp r, update rest f left r, update rest f right r)
          else evalTree t r) (* scarto il resto del cammino *)
  | _ -> failwith "Error: bad tree format"

and select (path : ide list) f (t : tree) (r : evT env) : treeVal =
  match t with
    Empty -> Empty
  | Node (ide, exp, left, right) ->
      (match path with
        [] -> Empty (* dominio vuoto, condizione vacuamente falsa *)
      | head :: rest ->
          if (head = ide)
            then let res = (eval (FunCall(f, exp)) r) in (* risultato della funzione booleana *)
              if (typecheck "bool" res) (* perché le funzioni possono restituire tipi diversi in base all'input *)
                then if (res = Bool(true))
                  then evalTree t r (* restituisco l'albero *)
                  else let tmp = (select rest f left r) in (* "cerco" a sinistra *)
                    (match tmp with
                      Empty -> select rest f right r (* se non trovo nulla continuo a destra *)
                    | NodeVal (_) -> tmp)
                else failwith "Error: boolean result expected"
            else Empty);; (* il nodo corrente non appartiene al cammino *)

(* =============================  TESTS  ============================= *)

(* definizione ambiente vuoto *)
let env0 = emptyenv Unbound;;

(* definizione funzione di incremento *)
let inc = Fun("x", Sum(Den "x", Eint 1));;

(* definizione funzione di raddoppio *)
let double = Fun("x", Prod(Den "x", Eint 2));;

(* definizione funzione isPositive: true se x >=0, false altrimenti *)
let isPositive = Fun("x", Ifthenelse(Leq(Den("x"), Eint(-1)), Ebool(false), Ebool(true)));;

(* definizione funzione isEven: true se x è pari, false altrimenti *)
let isEven = Fun("x", Ifthenelse(Eq(Modulus(Den("x"), Eint 2), Eint 0), Ebool(true), Ebool(false)));;

(* definizione albero di prova *)
let tree1 =
  ETree(Node("a", Prod(Eint (-5), Eint 5),
    Node("b", FunCall(double, Eint 1),
      Empty,
      Node("d", Letrec("fact", Fun("n", Ifthenelse(Eq(Den "n", Eint 0), Eint 1,
          Prod(Den "n", FunCall(Den "fact", Diff(Den "n", Eint 1))))),
          FunCall(Den "fact", Eint 5)), (* espressione: 5! *)
        Empty,
        Empty)),
    Node("c", Eint 3,
      Node("e", Eint 100,
        Empty,
        Empty),
      Empty)));;

(* definizione albero contenente cammini uguali *)
let tree2 =
  ETree(Node("a", Eint 1,
    Node("b", Eint 2,
      Node("c", Eint 3,Empty, Empty),
      Node("d", Eint 4,Empty, Empty)),
    Node("b", Eint 5,
      Node("c", Eint 6, Empty, Empty),
      Node("c", Eint 7, Empty, Empty))));;

(* valutazioni standard *)
eval tree1 env0;;
eval tree2 env0;;

(* incremento dei valori dell'intero albero *)
let e1 = ApplyOver(inc, tree1);;
eval e1 env0;;

(* raddoppio il valore del nodo "c" *)
let e2 = Update(["a"; "c"], double, tree1);;
eval e2 env0;;

(* raddoppio il valore di tutti e 3 i nodi "c" nell'albero con cammini uguali *)
let e2bis = Update(["a"; "b"; "c"], double, tree2);;
eval e2bis env0;;

(* cerco un sottoalbero che ha come radice un numero pari nel cammino "a" "b" "d" *)
(* risultato: il primo nodo del cammino che soddisfa la condizione e' "b",
   viene quindi restituito il sottoalbero che ha "b" come radice *)
let e3 = Select(["a"; "b"; "d"], isEven, tree1);;
eval e3 env0;;




