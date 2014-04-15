(* Structure d'une formule propositionnelle polymorphe *)
type valeur_prop = True | False;;

type 'a formule_prop =  Ou of 'a formule_prop * 'a formule_prop	
			| Et of 'a formule_prop * 'a formule_prop
			| Implique of 'a formule_prop * 'a formule_prop
			| Negation of 'a formule_prop
			| Equivalence of 'a formule_prop * 'a formule_prop
			| Variable of string 
			| Valeur of  valeur_prop;;


(* Affichage de la formule *)
let rec to_String (f:'a formule_prop) = 
    match f with 
    | Ou(p,q) -> "(" ^ (to_String p) ^ ") || (" ^ (to_String q) ^ ")"
    | Et(p,q) -> "(" ^ (to_String p) ^ ") && (" ^ (to_String q) ^ ")"
    | Negation p -> "!"^ (to_String p) 
    | Implique (p,q) -> "("^(to_String p) ^ ") => (" ^ (to_String q) ^ ")"
    | Equivalence (p,q) -> "("^(to_String p) ^ ") <=> (" ^ (to_String q) ^ ")"
    | Valeur True -> "True" 
    | Valeur False -> "False"
    | Variable x -> x
;;

(* Substitution de Implique et Equivalence par leurs correspondances *)
let rec sub f =
  match f with
  | Ou (p,q) -> Ou ((sub p), (sub q))
  | Et (p,q) -> Et ((sub p), (sub q))
  | Negation p -> Negation (sub p)
  | Implique (p,q) -> Ou ((sub (Negation p)), (sub q))
  | Equivalence (p,q) -> Et ( (sub (Implique (p,q))), (sub(Implique(q,p))))
  | Variable x -> Variable x
  | Valeur True -> Valeur True
  | Valeur False -> Valeur False
 ;;


(* Reduction de la formule *)
let rec reductionEquivalences f = 
  match f with 
  | Negation (Valeur False) -> Valeur True
  | Negation (Valeur True) -> Valeur False
  | Negation(p) -> Negation(reductionEquivalences p)
  | Ou (Valeur True, p) | Ou (p, Valeur True) -> Valeur True 
  | Et (Valeur False, p) | Et (p, Valeur False) -> Valeur False
  | Ou (Valeur False, p) | Ou (p, Valeur False) -> reductionEquivalences p
  | Et (Valeur True, p) | Et (p, Valeur True) -> reductionEquivalences p
   
  | Et(p, q) -> if p = q then reductionEquivalences p else Et((reductionEquivalences p), (reductionEquivalences q))
  | Ou(p, q) -> if p = q then reductionEquivalences p else Ou((reductionEquivalences p), (reductionEquivalences q))
  
  | Valeur x -> Valeur x
  | Variable x -> Variable x
;;

(* Stockage des variables propositionnelles *)
let rec ensembleVariables f  = 
  match f with 
  | Et(p,q) | Ou(p,q)-> (ensembleVariables p)@(ensembleVariables q)
  | Negation p -> ensembleVariables p
  | Variable q -> [q]
  | Valeur _ -> []
;;


let nb_occurence elm liste = 
  let rec aux nb elm liste = 
    match liste with 
    | [] -> nb
    | h::t -> if h = elm then aux (nb+1) elm t 
      else aux nb elm t 
  in aux 0 elm liste;;


let listeVariables f = 
  let rec aux assocVariables ensemblesV =
    match ensemblesV with 
    | [] -> assocVariables
    | h::t -> if (List.mem_assoc h assocVariables) then (aux assocVariables t )
      else aux ((h,(nb_occurence h ensemblesV))::assocVariables) t 
  in aux [] (ensembleVariables f);;


(* Algo de Satisfiabilite *)
let satisfiabilite = function formule -> 
  let rec aux Val F =
    match F with 
    | [] -> Val 
    | h::t -> let V = ensembleV
  in aux [] [sub formule]
;;





(* Zone de testes *)
let f1 = Et (( (True)), (Negation True));;
reductionEquivalences f1;;
let megaFormule =
 Et(
   (Implique 
      (Variable "Q", Variable "S")),
   (Equivalence
      (Negation (Variable "P"), Variable "S")));;

reductionEquivalences (sub megaFormule);;

listeVariables f2;;

let t = sub megaFormule;;
to_String too;;

let too =  Ou(Negation (Variable "R"),Negation(Variable"Q"));;
reductionEquivalences too;;
