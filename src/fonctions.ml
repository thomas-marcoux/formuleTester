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


(* Choix de la meilleur variable *)
let choixVariable listeV = 
  let rec aux listeV choix =
    match listeV with 
  | [] -> choix
  | (p,q)::t -> if q > snd choix then aux t (p,q)
    else aux t choix
  in aux listeV ("",0);;

(* Suppression d'une variable *) 
let suppVariable listeV choix = 
  let rec aux listeV listeCopie = 
    match listeV with 
    | [] -> listeCopie 
    | h::t -> if h = choix then (listeCopie@t) 
      else aux t (h::listeCopie)
  in aux listeV []
;;


(* Attribution de la variable x par une valeur*)
let attributionValeur f variableX valeurX =
  let rec aux f =
    match f with 
    |Valeur x -> Valeur x
    |Variable x -> if (x = variableX) then Valeur valeurX 
      else Variable x
    | Et(p,q) -> Et((aux p),(aux q))
    | Ou(p,q) -> Ou ((aux p),(aux q))
    | Negation p -> Negation (aux p)
  in aux f
;;



(* Algo de Satisfiabilite *)
let satisfiabilite = function formule -> 
  let rec aux valeurs f =
    match f with 
    | [] -> valeurs 
    | h::t -> let v = (listeVariables h) 
	      in let x = (choixVariable v)
		 in let v = (suppVariable v x)
		    in let f1 = (attributionValeur h x True)
		       in let f2 = (attributionValeur h x False)  
		
  in aux [] [sub formule]
;;





(* Zone de testes *)
let megaFormule =
 Et(
   (Implique 
      (Variable "Q", Variable "S")),
   (Equivalence
      (Negation (Variable "P"), Variable "S")));;

attributionValeur (reductionEquivalences (sub megaFormule)) "Q" True ;;

choixVariable(listeVariables (sub megaFormule));;
