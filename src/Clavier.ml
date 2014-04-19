(* Structure d'une formule propositionnelle polymorphe *)
type valeur_prop = True | False | Indefini;;


type 'a formule_prop =    Ou of 'a formule_prop * 'a formule_prop	
			| Et of 'a formule_prop * 'a formule_prop
			| Implique of 'a formule_prop * 'a formule_prop
			| Negation of 'a formule_prop
			| Equivalence of 'a formule_prop * 'a formule_prop
			| Variable of string
			| Valeur of valeur_prop;;


exception ConvertionImpossible;;


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
    | Valeur Indefini -> "Indefini"
    | Variable x -> x
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


let convertions (list:'a formule_prop list) = 
  let rec aux list = 
    match list with 
    | a::[] -> [a]
      (* Il ne reste qu'un element on test si c'est valeur/variable sinon on jette une exception 
      begin match a with 
      | Valeur x -> [a]
      | _ -> raise ConvertionImpossible 
      end*)
 
    | a::b::[] -> 
      (* On test si c'est une négation, un cas préremplis ou une valeur/variable sinon on jette une exception *)
      begin match a with 
      | Valeur x -> a::(aux [b])
      | Negation(Valeur Indefini) -> 
       (* Si le suivant est une valeur/variable on la met sinon on jete une exception *)
	begin match b with 
	| (Valeur True)
	| (Valeur False) -> [Negation b]
	| _ -> raise ConvertionImpossible
	end 
     | Negation(Valeur x) -> Negation(Valeur x)::(aux [b])(* Deja mis on continue *)

     (* Cas du Et presque remplis *)
     |Et(Valeur True, Valeur Indefini) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Et(Valeur True, b)]
       | _ -> raise ConvertionImpossible
       end
     |Et(Valeur False, Valeur Indefini) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Et(Valeur False, b)]
       | _ -> raise ConvertionImpossible
       end
     |Et(Valeur Indefini,Valeur True) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Et(b,Valeur True)]
       | _ -> raise ConvertionImpossible
       end
     |Et(Valeur Indefini,Valeur False) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Et(b,Valeur False)]
       | _ -> raise ConvertionImpossible
       end

     (* Cas du Ou presque remplis *) 
     |Ou(Valeur True, Valeur Indefini) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Ou(Valeur True, b)]
       | _ -> raise ConvertionImpossible
       end
     |Ou(Valeur False, Valeur Indefini) -> 
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Ou(Valeur False, b)]
       | _ -> raise ConvertionImpossible
       end
     |Ou(Valeur Indefini, Valeur True) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Ou(b,Valeur True)]
       | _ -> raise ConvertionImpossible
       end
     |Ou(Valeur Indefini, Valeur False) -> 
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Ou(b,Valeur False)]
       | _ -> raise ConvertionImpossible
       end

     (* Cas de l'implication presque remplis *) 
     |Implique(Valeur True, Valeur Indefini) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Implique(Valeur True, b)]
       | _ -> raise ConvertionImpossible
       end
     |Implique(Valeur False, Valeur Indefini) -> 
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Implique(Valeur False, b)]
       | _ -> raise ConvertionImpossible
       end
     |Implique(Valeur Indefini, Valeur True) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Implique(b,Valeur True)]
       | _ -> raise ConvertionImpossible
       end
     |Implique(Valeur Indefini, Valeur False) -> 
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Implique(b,Valeur False)]
       | _ -> raise ConvertionImpossible
       end

     (* Cas de l'équivalence presque remplis *) 
     |Equivalence(Valeur True, Valeur Indefini) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Equivalence(Valeur True, b)]
       | _ -> raise ConvertionImpossible
       end
     |Equivalence(Valeur False, Valeur Indefini) -> 
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Equivalence(Valeur False, b)]
       | _ -> raise ConvertionImpossible
       end
     |Equivalence(Valeur Indefini, Valeur True) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Equivalence(b,Valeur True)]
       | _ -> raise ConvertionImpossible
       end
     |Equivalence(Valeur Indefini, Valeur False) -> 
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> [Equivalence(b,Valeur False)]
       | _ -> raise ConvertionImpossible
       end
     
      end


    | a::b::c::t -> (* On test tous les cas *)
      begin match a with 
      (* Cas de la negation *)
      | Negation(Valeur Indefini) -> 
	(* On test si le suivant est reductible si oui on le met sinon on continue *)
	begin match( reductionEquivalences b) with 
	| (Valeur True)
	| (Valeur False) -> (Negation b)::c::t
	| Valeur Indefini -> a::(aux(b::c::t))
	end 
      | Negation(Valeur x) -> Negation(Valeur x)::b::c::t  (* Deja mis on continue *)

      | Et(Valeur Indefini, Valeur Indefini) -> (* Cas du Et vide *)
	(* On test si b et c sont reductible si oui on les met sinon on continue *)
	begin match (reductionEquivalences b, reductionEquivalences c) with
	| (Valeur True, Valeur True)
	| (Valeur False, Valeur False)
	| (Valeur True, Valeur False) 
	| (Valeur False, Valeur True) -> Et(b,c)::t (* Reductible = On le met *)
	| (Valeur Indefini, Valeur True)
	| (Valeur Indefini, Valeur False)
	| (Valeur True, Valeur Indefini) 
	| (Valeur False, Valeur Indefini) 
	| (Valeur Indefini, Valeur Indefini) -> a::(aux (b::c::t)) (* Irreductible on continue *)
	end
     |Et(Valeur True, Valeur Indefini) -> (* Cas du Et presque remplis *)
       begin match (reductionEquivalences b) with 
       | (Valeur True)
       | (Valeur False) -> Et(Valeur True, b)::c::t
       | _ -> a::(aux (b::c::t))
       end
     |Et(Valeur False, Valeur Indefini) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> Et(Valeur False, b)::c::t
       | _ -> a::(aux (b::c::t))
       end
     |Et(Valeur Indefini,Valeur True) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> Et(b,Valeur True)::c::t
       | _ -> a::(aux (b::c::t))
       end
     |Et(Valeur Indefini,Valeur False) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> Et(b,Valeur False)::c::t
       | _ -> a::(aux (b::c::t))
       end
     | Et( _,  _) -> a::b::c::t
     

      | Ou(Valeur Indefini, Valeur Indefini) ->  (* Cas du Ou remplis *)
	(* On test si b et c sont reductible si oui on les met sinon on continue *)
	begin match (reductionEquivalences b, reductionEquivalences c) with
	| (Valeur True, Valeur True) 
	| (Valeur False, Valeur False)
	| (Valeur True, Valeur False)
	| (Valeur False, Valeur True) -> Ou(b,c)::t (* Reductible = on les mets *)
	| (Valeur Indefini, Valeur True)
	| (Valeur Indefini, Valeur False) 
	| (Valeur True, Valeur Indefini)
	| (Valeur False, Valeur Indefini) 
	| (Valeur Indefini, Valeur Indefini) -> a::(aux (b::c::t)) (* Irreductible on continue *)
	end
     |Ou(Valeur True, Valeur Indefini) -> (* Cas du Ou presque remplis *)
       begin match (reductionEquivalences b) with 
       | (Valeur True)
       | (Valeur False) -> Ou(Valeur True, b)::c::t
       | _ -> a::(aux (b::c::t))
       end
     |Ou(Valeur False, Valeur Indefini) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> Ou(Valeur False, b)::c::t
       | _ -> a::(aux (b::c::t))
       end
     |Ou(Valeur Indefini,Valeur True) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> Ou(b,Valeur True)::c::t
       | _ -> a::(aux (b::c::t))
       end
     |Ou(Valeur Indefini,Valeur False) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> Ou(b,Valeur False)::c::t
       | _ -> a::(aux (b::c::t))
       end
     | Ou( _,_) -> a::b::c::t

      | Implique(Valeur Indefini, Valeur Indefini) -> (* Cas de l'implication remplis *)
	(* On test si b et c sont reductible si oui on les met sinon on continue *)
	begin match (reductionEquivalences b, reductionEquivalences c) with
	| (Valeur True, Valeur True) 
	| (Valeur False, Valeur False)
	| (Valeur True, Valeur False)
	| (Valeur False, Valeur True) -> Implique(b,c)::t (* Reductible = on les mets *)
	| (Valeur Indefini, Valeur True)
	| (Valeur Indefini, Valeur False) 
	| (Valeur True, Valeur Indefini)
	| (Valeur False, Valeur Indefini) 
	| (Valeur Indefini, Valeur Indefini) -> a::(aux (b::c::t)) (* Irreductible on continue *)
	end
     |Implique(Valeur True, Valeur Indefini) -> (* Cas de l'implication presque remplis *)
       begin match (reductionEquivalences b) with 
       | (Valeur True)
       | (Valeur False) -> Implique(Valeur True, b)::c::t
       | _ -> a::(aux (b::c::t))
       end
     |Implique(Valeur False, Valeur Indefini) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> Implique(Valeur False, b)::c::t
       | _ -> a::(aux (b::c::t))
       end
     |Implique(Valeur Indefini,Valeur True) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> Implique(b,Valeur True)::c::t
       | _ -> a::(aux (b::c::t))
       end
     |Implique(Valeur Indefini,Valeur False) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> Implique(b,Valeur False)::c::t
       | _ -> a::(aux (b::c::t))
       end
     | Implique(_,_) -> a::b::c::t


     | Equivalence(Valeur Indefini, Valeur Indefini) ->  (* Cas de l'équivalence remplis *)
	(* On test si b et c sont reductibles si oui on les mets sinon on continue *)
	begin match (reductionEquivalences b, reductionEquivalences c) with
	| (Valeur True, Valeur True) 
	| (Valeur False, Valeur False)
	| (Valeur True, Valeur False)
	| (Valeur False, Valeur True) -> Equivalence(b,c)::t (* Reductible = on les mets *)
	| (Valeur Indefini, Valeur True)
	| (Valeur Indefini, Valeur False) 
	| (Valeur True, Valeur Indefini)
	| (Valeur False, Valeur Indefini) 
	| (Valeur Indefini, Valeur Indefini) -> a::(aux (b::c::t)) (* Irreductible on continue *)
	end
     |Equivalence(Valeur True, Valeur Indefini) -> (* Cas de l'equivalence presque remplis *)
       begin match (reductionEquivalences b) with 
       | (Valeur True)
       | (Valeur False) -> Equivalence(Valeur True, b)::c::t
       | _ -> a::(aux (b::c::t))
       end
     |Equivalence(Valeur False, Valeur Indefini) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> Equivalence(Valeur False, b)::c::t
       | _ -> a::(aux (b::c::t))
       end
     |Equivalence(Valeur Indefini,Valeur True) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> Equivalence(b,Valeur True)::c::t
       | _ -> a::(aux (b::c::t))
       end
     |Equivalence(Valeur Indefini,Valeur False) ->
       begin match b with 
       | (Valeur True)
       | (Valeur False) -> Equivalence(b,Valeur False)::c::t
       | _ -> a::(aux (b::c::t))
       end
     |Equivalence(_,_) -> a::b::c::t
      end
  in aux list

;;


(* Applique autant que possible reductionEquivalences *)
let rec applicationConvertions (list: 'a formule_prop list) =
  let l2 = (convertions list) in
  if (l2 = list) then list else (applicationConvertions l2);;


(* Ajout de l'operation dans la liste de formule propositionnelles *)
let put_on_file (liste: 'a formule_prop list)  chaine =
  match chaine with
  | "False" -> liste @ [Valeur False]
  | "True" -> liste @ [Valeur True]
  | "Not" -> liste @ [Negation (Valeur Indefini)]
  | "And" -> liste @ [Et(Valeur Indefini, Valeur Indefini)]
  | "Or" -> liste @ [Ou(Valeur Indefini, Valeur Indefini)]
  | "Imp" -> liste @ [Implique(Valeur Indefini, Valeur Indefini)]
  | "Equi" -> liste @ [Equivalence(Valeur Indefini, Valeur Indefini)]
  | _ -> raise ConvertionImpossible;;


(* Affichage de la liste de formules propositionnelles *)
let string_of_list l =
  let rec aux l res = 
    match l with 
    | [] -> res
    | h::t -> aux t (res ^ (to_String h) ^ " | ")
  in aux l "Liste : ";; 

(* Exctraction de la formule propositionnelle *)
let extraction (liste:'a formule_prop list) = 
  List.hd liste;;

(* Boucle de saisie Clavier *)
let rec toplevel (f:'a formule_prop list) =  
  if f = [] then print_string "Formule Propositionnel Vide.\n\n"
  else print_string ((string_of_list f) ^ "\n\n");

  let s = read_line() in 
  if s = "exit" then print_string "Au revoir !\n"
  else if s = "end" then begin print_string (to_String(extraction(applicationConvertions f))^ " \n\n"); toplevel [] end
  else try toplevel (put_on_file f s) with 
  | ConvertionImpossible -> print_string "Erreur : Vous-vous êtes trompé(e)de commande, veuillez recommencer. \n"; toplevel f;;


(* On affiche le premier message *) 
let main() = print_string "Evaluation de formules :\n\n";  
toplevel [];;

(* On lance le programme *) 
main();;
