(* Structure d'une formule propositionnelle polymorphe *)
type 'a valeur_prop = True | False;;


type 'a formule_prop =    Ou of 'a formule_prop * 'a formule_prop	
			| Et of 'a formule_prop * 'a formule_prop
			| Implique of 'a formule_prop * 'a formule_prop
			| Negation of 'a formule_prop
			| Equivalence of 'a formule_prop * 'a formule_prop
			| Variable of 'a formule_prop
			| Valeur of valeur_prop;;
