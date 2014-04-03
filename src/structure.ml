type 'a valeur_prop =  True | False ;;

type 'a formule_prop = Ou of 'a formule_prop * 'a formule_prop	
	       | Et of 'a formule_prop * 'a formule_prop
		       | Implique of 'a formule_prop * 'a formule_prop
		       | Negaton of 'a formule_prop
		       | Equivalence of 'a formule_prop * 'a formule_prop
		       | Valeur of 'a valeur_prop
		       | Variable of 'a valeur_prop ;;
