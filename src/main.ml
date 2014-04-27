(*********************************
********* Structure .ml **********
**********************************)

(* Structure d'une formule propositionnelle polymorphe *)
type valeur_prop = True | False | Indefini;;


type 'a formule_prop =    Ou of 'a formule_prop * 'a formule_prop	
			| Et of 'a formule_prop * 'a formule_prop
			| Implique of 'a formule_prop * 'a formule_prop
			| Negation of 'a formule_prop
			| Equivalence of 'a formule_prop * 'a formule_prop
			| Variable of string
			| Valeur of valeur_prop;;



(**********************************
********* Fonctions.ml ************
***********************************)

(* Affichage de la formule *)
let rec to_String (formule: 'a formule_prop) = 
    match formule with 
    | Ou (p,q) -> "(" ^ (to_String p) ^ ") || (" ^ (to_String q) ^ ")"
    | Et (p,q) -> "(" ^ (to_String p) ^ ") && (" ^ (to_String q) ^ ")"
    | Negation p -> "!"^ (to_String p) 
    | Implique (p,q) -> "(" ^ (to_String p) ^ ") -> (" ^ (to_String q) ^ ")"
    | Equivalence (p,q) -> "(" ^ (to_String p) ^ ") <-> (" ^ (to_String q) ^ ")"
    | Valeur True -> "True" 
    | Valeur False -> "False"
    | Valeur Indefini -> "Indefini"
    | Variable x -> "Var " ^ x
;;

(* Utilisé pour afficher la liste de Couple *)
let rec to_StringCouple (liste: (string*bool) list) =
  match liste with 
  | [] -> ""
  | (x, true)::[] -> "(" ^ x ^ ": True)"
  | (x, false)::[] -> "(" ^ x ^ ": False)"
  | (x ,true)::t -> "(" ^ x ^ ": True), " ^ (to_StringCouple t)
  | (x, false)::t -> "(" ^ x ^ ": False), " ^ (to_StringCouple t)
;;


(* Affichage de la liste de couple *)
let rec to_StringCoupleListe (liste: (string*bool) list list) = 
  match liste with 
  | [] -> "" 
  | h::[] -> (to_StringCouple h)
  | h::t -> (to_StringCouple h) ^ " | " ^ (to_StringCoupleListe t)
;;




(* Substitution de "Implique" et "Equivalence" par leurs correspondances *)
let rec elimination (formule: 'a formule_prop) =
  match (formule: 'a formule_prop) with
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
let rec reductionEquivalences (formule: 'a formule_prop) = 
  match formule with 
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
let rec reductionFormule (formule: 'a formule_prop) =
  let formuleBis = reductionEquivalences formule in
  if (formuleBis = formule) then formuleBis else reductionFormule formuleBis
;;

(*************************************
********* Satisfiabilite.ml **********
**************************************)

(* Stockage des variables propositionnelles *)
let rec ensembleVariables (formule: 'a formule_prop) = 
  match formule with 
  | Et (p,q) | Ou(p,q)-> (ensembleVariables p) @ (ensembleVariables q)
  | Negation p -> ensembleVariables p
  | Variable q -> [q]
  | Valeur _ -> []
;;

(* Calcule le nombre d'occurence d'une variable *)
let nb_occurence (elm: 'a) (liste: 'a list) = 
  let rec aux nb elm liste = 
    match liste with 
    | [] -> nb
    | h::t -> if h = elm then aux (nb+1) elm t 
      else aux nb elm t 
  in aux 0 elm liste
;;

(* Trouve la liste des couples (variables, nombre d'occurences) *)
let listeVariables (formule: 'a formule_prop) = 
  let rec aux listeAssocVariables ensembleVariables =
    match ensembleVariables with 
    | [] -> listeAssocVariables
    | h::t -> if (List.mem_assoc h listeAssocVariables) then (aux listeAssocVariables t)
      else aux (listeAssocVariables @ [(h, (nb_occurence h ensembleVariables))]) t 
  in aux [] (ensembleVariables formule);;


(* Choix de la variable ayant le plus d'occurences *)
let choixVariable (listeVariables: (string*int) list) = 
  let rec aux listeVariables choix =
    match listeVariables with 
  | [] -> choix
  | (p,q)::t -> if q > (snd choix) then aux t (p,q)
    else aux t choix
  in aux listeVariables ("",0);;


(* Attribution de la variable x par une valeur (True/False) *)
let attributionValeur (formule: 'a formule_prop) (variableX: string) (valeurX: valeur_prop) =
  let rec aux formule =
    match formule with 
    | Valeur x -> Valeur x
    | Variable x -> if (x = variableX) then Valeur valeurX 
      else Variable x
    | Et (p,q) -> Et((aux p),(aux q))
    | Ou (p,q) -> Ou ((aux p),(aux q))
    | Negation p -> Negation (aux p)
  in aux formule
;;


(* Algorithme de Satisfiabilite *)
let satisfiabilite = function (formule: 'a formule_prop) -> 
  let rec aux valeur formuleEliminee =
    match formuleEliminee with 
    | [] -> []
    | h::t -> let x = (choixVariable (listeVariables h)) in
	      let f1 = (attributionValeur h (fst x) True) in
	      let f2 = (attributionValeur h (fst x) False) in
	      let f1 = reductionFormule f1  in
	      let f2 = reductionFormule f2  in
	      match (f1,f2) with 
	      | (Valeur False , Valeur False ) -> []
	      | (Valeur False , Valeur True  ) -> [ valeur @ [((fst x), false)]]  
	      | (Valeur True  , Valeur False ) -> [ valeur @ [((fst x), true)]]
	      | (Valeur True  , Valeur True  ) -> [ valeur @ [((fst x), true)]]  @  [valeur @ [((fst x), false)]] 
	      | (Valeur False , _            ) -> aux (valeur@[((fst x), false)]) ([f2])
	      | (_            , Valeur False ) -> aux (valeur@[((fst x), true)]) ([f1])
	      | (Valeur True  , _            ) ->  [valeur@[((fst x), true)]]  @ (aux (valeur@[((fst x), false)]) [f2])
	      | (_            , Valeur True  ) ->  [valeur@[((fst x), false) ]]@ (aux (valeur@[((fst x), true)]) [f1]) 
	      | (_            , _            ) -> ((aux (valeur@[((fst x), true)]) ([f1]) )) @ ((aux (valeur@[((fst x), false)]) ([f2]) ))		
  in aux [] [elimination formule]
;;

(* Verifie si deux liste simple (string * bool) list sont égales *)
let egals (listeUn:(string*bool) list) (listeDeux:(string*bool) list) =
  let rec aux listeDeux= 
    match listeDeux with 
    | [] -> true
    | h::t ->
      if (List.mem_assoc (fst h) listeUn) then 
	if ((List.assoc (fst h) listeDeux) = (List.assoc (fst h) listeUn)) then aux t else false
      else aux t   
  in aux listeDeux
;;

(* l1 est la plus grande liste, si il existe un elements de l2 qui n'existe pas dans l1 on l'ajoute *)
let ajoutListes l1 l2 =
  let rec aux l2 mem =  
  match l2 with 
  | [] -> mem
  | h::t -> if List.mem_assoc (fst h) l1 then aux t mem
    else aux t mem@[h] 
  in aux l2 l1 
;;

(* Si la listeCouple egale une liste de newListe on ajoute la plus grande *)
let correspond (listeCouples:(string*bool) list) (newListe:(string*bool) list list) =
  let rec aux newListe listMem = 
    match newListe with 
    | []  -> listMem
    | h::t -> if egals h listeCouples then
	if(List.length h) > (List.length listeCouples)then aux t (listMem @ [ajoutListes h listeCouples ])
	else aux t (listMem @ [ajoutListes listeCouples h])
      else aux t listMem
  in aux newListe []
;;

(* Pour toute liste de listeCouples on test si elle correspond à newListe
   si oui on ajoute celles qui correspondes *)
let rec suppListeCouple (newListe:(string*bool) list list) (listeCouples:(string*bool) list list) (listeMem:(string*bool) list list) = 
  match listeCouples with 
  | [] -> listeMem
  | h::t -> suppListeCouple newListe t (listeMem @ (correspond h newListe))
;;

(* Algorithme d'ensemble de Satisfiabilite *)
 let ensembleSatisfiabilite (listeFonc: 'a formule_prop list) =
  let rec aux listeFonc affichage listeCouple = 
    match listeFonc with 
    | [] -> affichage ^ to_StringCoupleListe(listeCouple)
    | h::t ->  (aux t (affichage ^ (to_String h) ^ "  **  ") (suppListeCouple (satisfiabilite h) listeCouple []))
  in aux listeFonc "" (satisfiabilite (List.hd listeFonc))
;;  

ensembleSatisfiabilite [Et(Variable "a", Variable "v"); Et(Variable "a", Variable "c")];;
(*********************************
********* Balayage.ml ************
**********************************)

let balayage = fun f1
  -> let f = elimination f1
     in let rec aux = fun l
	  -> match l with
	       [] -> false
	     | h::t -> let f2 = reductionFormule
				  (Et (attributionValeur f (fst h) True,
				       attributionValeur f (fst h) False))
		       in if f2 = Valeur True then true
			  else if reductionFormule
				    (Negation (f2)) = Valeur True
			  then true
			  else aux t
	in aux (listeVariables f);;

(************************************
********* SaisieClavier.ml **********
*************************************)

exception ConvertionImpossible;;
exception FormuleIncomplete;;
exception FormuleIncorrecte;;
exception ListeVideError;;

(* Reduction de la formule d'un cran *)
let rec formuleCorrecte (formule: 'a formule_prop) = 
  match formule with
  | Valeur Indefini -> false
  | Valeur _ -> true
  | Variable _ -> true
  | Negation p -> formuleCorrecte p
  | Ou(p, q) -> (formuleCorrecte p) && (formuleCorrecte q)
  | Et(p, q) -> (formuleCorrecte p) && (formuleCorrecte q)
  | Implique (p,q) -> (formuleCorrecte p) && (formuleCorrecte q) 
  | Equivalence (p,q) ->(formuleCorrecte p) && (formuleCorrecte q)
;;

(* Methode pour réduire vers une seul formule propositionnelle *)
let convertions (liste:'a formule_prop list) = 
  let rec aux liste = 
    match liste with 
    | [] -> []
    | a::[] -> 
      begin match (formuleCorrecte a) with 
      | true -> [a]
      | false  -> raise FormuleIncomplete
      end

    | a::b::[] -> 
      begin match a with 
      (* Cas du "Negation" Non remplis *)
      | Negation(Valeur Indefini) -> 
	begin match (formuleCorrecte b) with
	| true -> [Negation b]
	| false -> raise FormuleIncorrecte
	end
      
      (* Cas du "Et" presque remplis *)
      |Et(Valeur True, Valeur Indefini) ->
	begin match (formuleCorrecte b) with 
	| true -> [Et(Valeur True, b)]
	| false -> raise FormuleIncorrecte
	end
      |Et(Valeur False, Valeur Indefini) ->
	begin match (formuleCorrecte b) with
	| true -> [Et(Valeur False, b)]
	| false -> raise FormuleIncorrecte
	end
      |Et(Valeur Indefini,Valeur True) ->
	begin match (formuleCorrecte b) with 
	| true -> [Et(b, Valeur True)]
	| false -> raise FormuleIncorrecte
	end
      |Et(Valeur Indefini,Valeur False) ->
	begin match (formuleCorrecte b) with 
	| true -> [Et(b, Valeur False)]
	| false -> raise FormuleIncorrecte
	end

      (* Cas du "Ou" presque remplis *)
      |Ou(Valeur True, Valeur Indefini) ->
	begin match (formuleCorrecte b) with 
	| true -> [Ou(Valeur True, b)]
	| false -> raise FormuleIncorrecte
	end
      |Ou(Valeur False, Valeur Indefini) ->
	begin match (formuleCorrecte b) with
	| true -> [Ou(Valeur False, b)]
	| false -> raise FormuleIncorrecte
	end
      |Ou(Valeur Indefini,Valeur True) ->
	begin match (formuleCorrecte b) with 
	| true -> [Ou(b, Valeur True)]
	| false -> raise FormuleIncorrecte
	end
      |Ou(Valeur Indefini,Valeur False) ->
	begin match (formuleCorrecte b) with 
	| true -> [Ou(b, Valeur False)]
	| false -> raise FormuleIncorrecte
	end

      (* Cas du "Implique" presque remplis *)
      |Implique(Valeur True, Valeur Indefini) ->
	begin match (formuleCorrecte b) with 
	| true -> [Implique(Valeur True, b)]
	| false -> raise FormuleIncorrecte
	end
      |Implique(Valeur False, Valeur Indefini) ->
	begin match (formuleCorrecte b) with
	| true -> [Implique(Valeur False, b)]
	| false -> raise FormuleIncorrecte
	end
      |Implique(Valeur Indefini,Valeur True) ->
	begin match (formuleCorrecte b) with 
	| true -> [Implique(b, Valeur True)]
	| false -> raise FormuleIncorrecte
	end
      |Implique(Valeur Indefini,Valeur False) ->
	begin match (formuleCorrecte b) with 
	| true -> [Implique(b, Valeur False)]
	| false -> raise FormuleIncorrecte
	end

      (* Cas du "Equivalence" presque remplis *)
      |Equivalence(Valeur True, Valeur Indefini) ->
	begin match (formuleCorrecte b) with 
	| true -> [Equivalence(Valeur True, b)]
	| false -> raise FormuleIncorrecte
	end
      |Equivalence(Valeur False, Valeur Indefini) ->
	begin match (formuleCorrecte b) with
	| true -> [Equivalence(Valeur False, b)]
	| false -> raise FormuleIncorrecte
	end
      |Equivalence(Valeur Indefini,Valeur True) ->
	begin match (formuleCorrecte b) with 
	| true -> [Equivalence(b, Valeur True)]
	| false -> raise FormuleIncorrecte
	end
      |Equivalence(Valeur Indefini,Valeur False) ->
	begin match (formuleCorrecte b) with 
	| true -> [Equivalence(b, Valeur False)]
	| false -> raise FormuleIncorrecte
	end
      
      (* Cas "Negation", "Et", "Ou", "Implique", "Equivalence", "Valeur", "Variable" déjà remplis *)
      | (Negation _) | (Et(_,_)) | (Ou(_,_)) | (Implique(_,_)) | (Equivalence(_,_)) | (Valeur _) | (Variable _) -> a::(aux [b])
      end

    | a::b::c::t -> (* On test tous les cas *)
      begin match a with 
      (* Cas de la negation *)
      | Negation(Valeur Indefini) -> 
	begin match (formuleCorrecte b) with 
	| true -> (Negation b)::c::t
	| false -> a::(aux(b::c::t))
	end 
	
      (* Cas du "Et" vide *)
      | Et(Valeur Indefini, Valeur Indefini) ->
	begin match (formuleCorrecte b, formuleCorrecte c) with
	| (true , true) -> Et(b,c)::t (* Reductible = On le met *)
	| (false, true)
	| (true , false)
	| (false, false) -> a::(aux (b::c::t)) (* Irreductible on continue *)
	end

      (* Cas du "Ou" vide *)
      | Ou(Valeur Indefini, Valeur Indefini) -> 
	begin match (formuleCorrecte b, formuleCorrecte c) with
	| (true , true) -> Ou(b,c)::t (* Reductible = on les mets *)
	| (false, true) 
	| (true, false)
	| (false ,false) -> a::(aux (b::c::t)) (* Irreductible on continue *)
	end

      (* Cas de "Implique" vide *)
      | Implique(Valeur Indefini, Valeur Indefini) -> 
	begin match (formuleCorrecte b, formuleCorrecte c) with
	| (true, true) -> Implique(b,c)::t (* Reductible = on les mets *)
	| (false ,true)
	| (true, false)
	| (false, false) -> a::(aux (b::c::t)) (* Irreductible on continue *)
	end

      (* Cas de "Equivalence" vide *)
      | Equivalence(Valeur Indefini, Valeur Indefini) ->
	begin match (formuleCorrecte b, formuleCorrecte c) with
	| (true, true) -> Equivalence(b,c)::t (* Reductible = on les mets *)
	| (false, true)
	| (true, false)
	| (false , false) -> a::(aux (b::c::t)) (* Irreductible on continue *)
	end

      (* Cas du "Et" presque remplis *)
      |Et(Valeur True, Valeur Indefini) ->
	begin match (formuleCorrecte b) with 
	| true -> Et(Valeur True, b)::c::t
	| false -> a::(aux (b::c::t))
	end
      |Et(Valeur False, Valeur Indefini) ->
	begin match (formuleCorrecte b) with
	| true -> Et(Valeur False, b)::c::t
	| false -> a::(aux (b::c::t))
	end
      |Et(Valeur Indefini,Valeur True) ->
	begin match (formuleCorrecte b) with 
	| true -> Et(b, Valeur True)::c::t
	| false -> a::(aux (b::c::t))
	end
      |Et(Valeur Indefini,Valeur False) ->
	begin match (formuleCorrecte b) with 
	| true -> Et(b, Valeur False)::c::t
	| false -> a::(aux (b::c::t))
	end

      (* Cas du "Ou" presque remplis *)
      |Ou(Valeur True, Valeur Indefini) ->
	begin match (formuleCorrecte b) with 
	| true -> Ou(Valeur True, b)::c::t
	| false -> a::(aux (b::c::t))
	end
      |Ou(Valeur False, Valeur Indefini) ->
	begin match (formuleCorrecte b) with
	| true -> Ou(Valeur False, b)::c::t
	| false -> a::(aux (b::c::t))
	end
      |Ou(Valeur Indefini,Valeur True) ->
	begin match (formuleCorrecte b) with 
	| true -> Ou(b, Valeur True)::c::t
	| false -> a::(aux (b::c::t))
	end
      |Ou(Valeur Indefini,Valeur False) ->
	begin match (formuleCorrecte b) with 
	| true -> Ou(b, Valeur False)::c::t
	| false -> a::(aux (b::c::t))
	end

      (* Cas du "Implique" presque remplis *)
      |Implique(Valeur True, Valeur Indefini) ->
	begin match (formuleCorrecte b) with 
	| true -> Implique(Valeur True, b)::c::t
	| false -> a::(aux (b::c::t))
	end
      |Implique(Valeur False, Valeur Indefini) ->
	begin match (formuleCorrecte b) with
	| true -> Implique(Valeur False, b)::c::t
	| false -> a::(aux (b::c::t))
	end
      |Implique(Valeur Indefini,Valeur True) ->
	begin match (formuleCorrecte b) with 
	| true -> Implique(b, Valeur True)::c::t
	| false -> a::(aux (b::c::t))
	end
      |Implique(Valeur Indefini,Valeur False) ->
	begin match (formuleCorrecte b) with 
	| true -> Implique(b, Valeur False)::c::t
	| false -> a::(aux (b::c::t))
	end

      (* Cas du "Equivalence" presque remplis *)
      |Equivalence(Valeur True, Valeur Indefini) ->
	begin match (formuleCorrecte b) with 
	| true -> Equivalence(Valeur True, b)::c::t
	| false -> a::(aux (b::c::t))
	end
      |Equivalence(Valeur False, Valeur Indefini) ->
	begin match (formuleCorrecte b) with
	| true -> Equivalence(Valeur False, b)::c::t
	| false -> a::(aux (b::c::t))
	end
      |Equivalence(Valeur Indefini,Valeur True) ->
	begin match (formuleCorrecte b) with 
	| true -> Equivalence(b, Valeur True)::c::t
	| false -> a::(aux (b::c::t))
	end
      |Equivalence(Valeur Indefini,Valeur False) ->
	begin match (formuleCorrecte b) with 
	| true -> Equivalence(b, Valeur False)::c::t
	| false -> a::(aux (b::c::t))
	end

      (* Cas "Negation", "Et", "Ou", "Implique", "Equivalence", "Valeur", "Variable" déjà remplis *)
      | (Negation _) | (Et(_,_)) | (Ou(_,_)) | (Implique(_,_)) | (Equivalence(_,_)) | (Valeur _) | (Variable _) -> a::(aux (b::c::t))
      end
  in aux liste
;;


(* Applique autant que possible formuleCorrecte et convertions *)
let rec applicationConvertions (liste: 'a formule_prop list) =
  let listeDeux = (convertions liste) in
  if (listeDeux = liste) then 
    begin
      match (formuleCorrecte (List.hd liste)) with
      | true -> liste
      | false -> raise FormuleIncomplete
    end 
  else (applicationConvertions listeDeux);;

(* Supprime le dernier element de la liste *)
let rec remove (liste: 'a formule_prop list)  =
  let rec aux liste mem =
    match liste with 
    | [] -> raise ListeVideError
    | h::t -> if t <> [] then aux t (mem @ [h]) else mem
  in aux liste [];; 

(* Ajout de l'operation dans la liste de formule propositionnelles *)
let put_on_file (liste: 'a formule_prop list)  chaine =
  match chaine with
  | "False" -> liste @ [Valeur False]
  | "True" -> liste @ [Valeur True]
  | "Var" -> print_string "<Code Variable> ";
    let s = read_line() in 
    liste @ [Variable s]
  | "Not" -> liste @ [Negation (Valeur Indefini)]
  | "And" -> liste @ [Et(Valeur Indefini, Valeur Indefini)]
  | "Or" -> liste @ [Ou(Valeur Indefini, Valeur Indefini)]
  | "Imp" -> liste @ [Implique(Valeur Indefini, Valeur Indefini)]
  | "Equi" -> liste @ [Equivalence(Valeur Indefini, Valeur Indefini)]
  | "remove" -> remove liste
  | _ -> raise ConvertionImpossible;;


(* Affichage de la liste de formules propositionnelles *)
let string_of_list liste =
  let rec aux liste res = 
    match liste with 
    | [] -> res
    | h::t -> aux t (res ^ (to_String h) ^ " | ")
  in aux liste "Liste : ";; 


(* Text d'aide *)
let textHelp =
  let str =  "\n\n -- Mode d'emploi du logiciel de valuation de formules -- \n\n

 Fonctions du Logiciel :

help : Affiche le mode d'emploi du logiciel.
again : Permet de commencer une nouvelle formule.
remove : Supprime le dernier opérateur inséré.
end : Permet d'évaluer les diverses formules.
True : Ajoute la Valeur True.
False : Ajoute la Valeur False.
Var : String : Ajoute le string en Variable tel Variable \"String\".
Not : Ajoute l'opérateur Negation().
And : Ajoute l'opérateur Et().
Or : Ajoute l'opérateur Ou().
Imp : Ajoute l'opérateur Implique().
Equi : Ajoute l'opérateur Equivalence().
exit : Permet de mettre fin au programme. \n

 Exemple: Ou(!P, Et(True, Q) veuillez taper:
<code> Or
<code> Not
<code> Var
<code Variable> P
<code> And
<code> True
<code> Var
<code Variable> Q
<code> end (Pour afficher le résultat de cette unique fonction)

\n\n -- Fin du mode d'emploi -- \n\n"
  in str
;;

(* Boucle de saisie Clavier *)
let rec toplevel (liste:'a formule_prop list) (listeFormule: 'a formule_prop list) =  
  if liste = [] then print_string "\nVeuillez rentrer une fonction.\n\n"
  else print_string ((string_of_list liste) ^ "\n\n");
  
  print_string "<Code> ";
  let s = read_line() in 
  if s = "exit" then print_string "\n Merci et au revoir !\n"
  else if s = "help" then begin print_string (textHelp); toplevel liste listeFormule end
  else if s = "again" then
    if (List.length liste) = 0 then begin print_string "Erreur : Vous n'avez pas rentrer de formule. \n"; toplevel liste listeFormule end
    else
      if balayage (List.hd (applicationConvertions liste)) = true then toplevel [] ((applicationConvertions liste)@listeFormule)
      else begin print_string "Votre formule est valide\n"; toplevel [] listeFormule; end
  else if s = "end" then
    if (List.length liste) = 0 then begin print_string "Erreur : Vous n'avez pas rentrer de formule. \n"; toplevel liste listeFormule end
    else begin print_string ((ensembleSatisfiabilite ((applicationConvertions liste)@listeFormule))); toplevel [] [] end
  else try toplevel (put_on_file liste s) listeFormule with 
  | ConvertionImpossible -> print_string "Erreur : Vous-vous êtes trompé(e)de commande, veuillez recommencer. \n"; toplevel liste listeFormule
  | FormuleIncomplete ->  print_string "Erreur : Votre formule n'est pas complète veuillez recommencer. \n"; toplevel liste listeFormule
  | FormuleIncorrecte ->  print_string "Erreur : Vous-vous êtes trompé(e) dans la formule, veuillez recommencer. \n"; toplevel liste listeFormule
  | ListeVideError -> print_string "Erreur : Vous n'avez rien à supprimer. \n"; toplevel liste listeFormule ;;






(*************************************
********* Main.ml ********************
**************************************)

(* Test 1 *)
let t1 =
  Equivalence (
    Et(
      Implique(
	Variable "p",
	Variable "q"), 
      Et(
	Et(
	  Variable "p",
	  Implique(
	    Variable "q",
	    Variable"r")), 
	Implique(
	  Variable "r",
	  Negation(
	    Variable "p"))))
      ,Negation(
	Variable"p"));;

ensembleSatisfiabilite [t1];;

(* Test 2 *)
let t2 =
  Ou(
    Implique(
      Et(
	Negation(Variable "r"),
	Negation(Variable "s")), 
      Variable "p"),
    Implique(
      Variable "q",
      Variable "r"));;

ensembleSatisfiabilite [t2];;

(* Test 3 *)
let t3 = 
  Et(
    Implique(
      Variable "q",
      Variable "s"),
    Implique(
      Negation(Variable "p"),
      Variable "r"));;

ensembleSatisfiabilite [t3];;

(* Test 4 *)
let t4 =
  Et(
    Ou(
      Negation(Variable "p"),
      Et(Variable "q", Variable "r")),
    Negation(Variable "q"));;

ensembleSatisfiabilite [t4];;

(* Test 5 *)
let f11 = Et(Variable "p", Implique(Variable "q", Variable "r"));;
let f12 = Negation(Variable "p");;

ensembleSatisfiabilite [f11;f12];;

(* Test 6 *)
let f21 = Implique(Equivalence(Variable "q", Variable "r"), Variable "p");;
let f22 = Implique(Variable "q", Variable "r");;

ensembleSatisfiabilite [f21;f22];;


(* Test 7 *) 
let t7 =
  Equivalence (
    Et(
      Variable "p",
      Variable "q"),
    Ou(
      Variable "p",
      Variable "r"));;

ensembleSatisfiabilite [t7];;

(* Test 8 *)
let t8 = 
  Et(
    Implique(
      Valeur True,
      Variable "p"),
    Equivalence(
      Valeur True,
      Ou(
	Variable "q",
	Variable "r")));;

ensembleSatisfiabilite [t8];;

(* Test 9 *)
let f31 = Implique(Variable "p", Variable "q");;
let f32 = Equivalence(Variable "p", Variable "q");;

ensembleSatisfiabilite [f31;f32];;

(* test 10 *)
let f41 = 
  Ou(
    Negation(Variable "f"),
    Implique(
      Variable "f",
      Variable "p"));;
let f42 = 
  Negation(
    Implique(
      Et(
	Variable "f",
	Variable "p"),
      Negation(Variable "p")));;

ensembleSatisfiabilite [f41;f42];;

(* Test 11 *)
let t11 =
  Equivalence(
    Ou(
      Negation( Variable "p"),
      Negation( Variable "q")),
    Et(
      Negation (Variable "r"),
      Variable "q"));;

ensembleSatisfiabilite [t11];;

(* Test 12 *)
let f51 = 
  Equivalence(
    Et(
      Variable "p",
      Variable "q"),
    Et( 
      Negation (Variable "p"),
      Variable "q"));;
let f52 = 
  Implique(
    Valeur True,
    Variable "q");;

ensembleSatisfiabilite [f51; f52];;

(* Test 13 *)
let t13 = Equivalence(Implique(Variable "p", Variable "q"),Implique(Variable "r", Variable "s"));;

ensembleSatisfiabilite [t13];;

(* Test 14 *)
let t14 = Negation(Implique(Ou(Variable "p", Variable "q"), Ou(Negation(Variable "s"),Negation(Variable "t"))));;

ensembleSatisfiabilite [t14];;

(* Test 15 *)
let f61 = Ou(Variable "p", Variable "q");;
let f62 = Negation(Variable "p");;
let f63 = Implique( Variable "p", Variable "t");;
let f64 = Equivalence (Valeur True, Variable "q");;

ensembleSatisfiabilite [f61;f62;f63;f64];;





(* On affiche le premier message *) 
let main() = print_string "-- Logiciel de Valuation de formules --  (help : Mode d'emploi)\n";  toplevel [] [];;

(* On lance le programme *) 
main();;
