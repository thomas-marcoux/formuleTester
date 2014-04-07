(* Structure d'une formule propositionnelle polymorphe *)
type 'a valeur_prop =  True | False ;;

type 'a formule_prop =    Ou of 'a formule_prop * 'a formule_prop	
			| Et of 'a formule_prop * 'a formule_prop
			| Implique of 'a formule_prop * 'a formule_prop
			| Negation of 'a formule_prop
			| Equivalence of 'a formule_prop * 'a formule_prop
			| Valeur of 'a valeur_prop;;
			

let f1 = Equivalence( Negation( Et( Valeur True, Valeur False)), Valeur False);;
let f2 = Implique( Valeur True, Valeur False);;


(* Substitution de Implique et Equivalence par leurs correspondances *)
let rec sub (f: 'a formule_prop) =
  match f with
  | Ou (p,q) -> Ou ((sub p), (sub q))
  | Et (p,q) -> Et ((sub p), (sub q))
  | Negation p -> Negation (sub p)
  | Implique (p,q) -> Ou (Negation (sub p), (sub q))
  | Equivalence (p,q) -> let f = Implique(p,q) in
			 let f2 = Implique(q,p) in  
			 Et ((sub f),(sub f2 ))
  | Valeur v -> Valeur v
 ;;
 
sub f1;;
sub f2;;
