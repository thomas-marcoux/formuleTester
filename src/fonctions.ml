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
    | Ou (p,q) -> "(" ^ (to_String p) ^ ") || (" ^ (to_String q) ^ ")"
    | Et (p,q) -> "(" ^ (to_String p) ^ ") && (" ^ (to_String q) ^ ")"
    | Negation p -> "!"^ (to_String p) 
    | Implique (p,q) -> "("^(to_String p) ^ ") => (" ^ (to_String q) ^ ")"
    | Equivalence (p,q) -> "("^(to_String p) ^ ") <=> (" ^ (to_String q) ^ ")"
    | Valeur True -> "True" 
    | Valeur False -> "False"
    | Variable x -> x
;;

(* Substitution de Implique et Equivalence par leurs correspondances *)
let rec elimination f =
  match f with
  | Ou (p,q) -> Ou ((elimination p), (elimination q))
  | Et (p,q) -> Et ((elimination p), (elimination q))
  | Negation p -> Negation (elimination p)
  | Implique (p,q) -> Ou ((elimination (Negation p)), (elimination q))
  | Equivalence (p,q) -> Et ((elimination (Implique (p,q))), (elimination (Implique(q,p))))
  | Variable x -> Variable x
  | Valeur True -> Valeur True
  | Valeur False -> Valeur False
 ;;


(* Reduction de la formule d'un cran *)
let rec reductionEquivalences f = 
  match f with 
  | Negation (Valeur False) -> Valeur True
  | Negation (Valeur True) -> Valeur False
  | Negation p -> Negation(reductionEquivalences p)
  | Ou (Valeur True, p) | Ou (p, Valeur True) -> Valeur True 
  | Et (Valeur False, p) | Et (p, Valeur False) -> Valeur False
  | Ou (Valeur False, p) | Ou (p, Valeur False) -> reductionEquivalences p
  | Et (Valeur True, p) | Et (p, Valeur True) -> reductionEquivalences p
  | Et(p, q) -> if p = q then reductionEquivalences p else Et((reductionEquivalences p), (reductionEquivalences q))
  | Ou(p, q) -> if p = q then reductionEquivalences p else Ou((reductionEquivalences p), (reductionEquivalences q))
  | Valeur x -> Valeur x
  | Variable x -> Variable x
;;


(* Applique autant que possible reductionEquivalences *)
let rec reductionFormule f =
  let f2 = reductionEquivalences f in
  if (f2 = f) then f2 else reductionFormule f2;;


(* Stockage des variables propositionnelles *)
let rec ensembleVariables f  = 
  match f with 
  | Et (p,q) | Ou(p,q)-> (ensembleVariables p) @ (ensembleVariables q)
  | Negation p -> ensembleVariables p
  | Variable q -> [q]
  | Valeur _ -> []
;;

(* Calcule le nombre d'occurence d'une variable *)
let nb_occurence elm liste = 
  let rec aux nb elm liste = 
    match liste with 
    | [] -> nb
    | h::t -> if h = elm then aux (nb+1) elm t 
      else aux nb elm t 
  in aux 0 elm liste;;

(* Trouve la liste des couples (variables, nombre d'occurences) *)
let listeVariables f = 
  let rec aux assocVariables ensemblesV =
    match ensemblesV with 
    | [] -> assocVariables
    | h::t -> if (List.mem_assoc h assocVariables) then (aux assocVariables t )
      else aux ((h,(nb_occurence h ensemblesV))::assocVariables) t 
  in aux [] (ensembleVariables f);;


(* Choix de la variable ayant le plus d'occurences *)
let choixVariable listeV = 
  let rec aux listeV choix =
    match listeV with 
  | [] -> choix
  | (p,q)::t -> if q > snd choix then aux t (p,q)
    else aux t choix
  in aux listeV ("",0);;


(* Attribution de la variable x par une valeur (True/False) *)
let attributionValeur f variableX valeurX =
  let rec aux f =
    match f with 
    | Valeur x -> Valeur x
    | Variable x -> if (x = variableX) then Valeur valeurX 
      else Variable x
    | Et (p,q) -> Et((aux p),(aux q))
    | Ou (p,q) -> Ou ((aux p),(aux q))
    | Negation p -> Negation (aux p)
  in aux f
;;



(* Algorithme de Satisfiabilite *)
let satisfiabilite = function formule -> 
  let rec aux valeur l =
    match l with 
    | [] -> []
    | h::t -> let x = (choixVariable (listeVariables h)) in
	      let f1 = (attributionValeur h (fst x) True) in
	      let f2 = (attributionValeur h (fst x) False) in
	      let f1 = reductionFormule f1  in
	      let f2 = reductionFormule f2  in
	      match (f1,f2) with 
	      | (Valeur False , Valeur False ) -> []
	      | (Valeur False , Valeur True  ) -> [ valeur @ [((fst x),false)] ] 
	      | (Valeur True  , Valeur False ) -> [ valeur @ [((fst x),true)] ]
	      | (Valeur True  , Valeur True  ) -> [ valeur @ [((fst x),true)] ] @ [ valeur @ [((fst x),false)] ]	    
	      | (Valeur False , _            ) -> aux (valeur@[((fst x),false)]) ([f2])
	      | (_            , Valeur False ) -> aux (valeur@[((fst x),true)]) ([f1])
	      | (Valeur True  , _            ) -> [ valeur@[((fst x),true)] ] @ (aux (valeur@[((fst x),false)]) [f2])
	      | (_            , Valeur True  ) -> [ valeur@[((fst x),false)] ]@ (aux (valeur@[((fst x),true)]) [f1]) 
	      | (_            , _            ) -> ((aux (valeur@[((fst x),true)]) ([f1]) )) @ ((aux (valeur@[((fst x),false)]) ([f2]) ))
		
  in aux [] [elimination formule]
;;


(* Algorithme principal de Satisfiabilite *)
let ensembleSatisfiabilite = function liste ->
  let rec aux = fun liste assocList ->
    match liste with
    | [] -> assocList
    | h::t -> aux t (assocList@[((to_String h),(satisfiabilite h))])
  in aux liste [];;





(* Zone de tests *)

(* Exemple 1*)
let megaFormule =
 Et(
   (Implique 
      (Variable "Q", Variable "P")),
   (Equivalence
      (Negation (Variable "P"), Variable "S")));;
ensembleSatisfiabilite [megaFormule];;


(* Exemple 2 *)
let formule = Ou (Variable "Q",Variable "P");;
satisfiabilite formule;;
let f2 = Et (Negation (Variable "P"),Variable "P");; (*Toujours fausse*)
satisfiabilite f2;;
ensembleSatisfiabilite [megaFormule;formule;f2];;

