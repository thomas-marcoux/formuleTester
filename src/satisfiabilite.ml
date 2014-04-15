



(* Reduction de la formule *)
let rec reductionEquivalences f = 
  match f with 
  | Negation (False) -> True
  | Ou (p, True) -> True
  | Ou (True, p) -> True
  | Et (p, True) -> reductionEquivalences p
  | Et (True, p) -> reductionEquivalences p
  | Et(p, q) -> if (comparaison p q) then reductionEquivalences p
  | Negation (True) -> False
  | Ou (p, False) -> reductionEquivalences p
  | Ou (False, p) -> reductionEquivalences p
  | Et (p, False) -> False
  | Et (False, p) -> False
;;


let rec comparaison p q = 
  match (p,q) with 
  | (True, True) -> true
  | (False,False) -> true
  | (True,False) -> false
  | (False,True) -> false
  | (Et(a,b), Et(c,d)) -> (test a c) && (test b d)
  | (Ou(a,b), Ou(c,d)) -> (test a c) && (test b d)
  | (Negation a, Negation b) -> test a b
;;     

(* Stockage des variables propositionnelles *)
let stockage f = 
  let rec aux f mem = 
    match f with 
    | Variable v -> if List.mem v mem then v::mem:à
    | Et(p,q) -> begin aux p, aux q end
    | Ou(p,q) -> begin aux p, aux q end
    | Negation p -> aux p
  in aux f [];;
      

(* Algo de Satisfiabilite *)
let satisfiabilite = function formule -> 
  let rec aux Val F =
    match F with 
    | [] -> Val 
    | h::t -> 
  in aux [] [sub formule]
;;





(* Zone de testes *)
let f1 = Et (( (True)), (Negation True));;
reductionEquivalences f1;;
