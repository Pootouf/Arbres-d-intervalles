open Intervalle
open ArbreRN

(* IntervalleArbre: Interface du module sur les arbres d'intervalle, héritant du code sur les intervalles d'arbres *)
module type IntervalleArbre = sig
  include Arbre

  type inter = elementA
  type element

  val inter : element -> element -> bool -> bool -> inter option
  val random_intervalle : int -> inter
  val recup_inter : ab -> inter
  val est_dans_arbre_intervalle : element -> ab -> bool
  val ajout : inter -> ab -> ab
  val retrait : inter -> ab -> ab
  val union : ab -> ab -> ab
  val intersection : ab -> ab -> ab
  val difference : ab -> ab -> ab
  val to_string : ab -> string
  val valide_arbres_inter : unit -> unit
  val string_of_inter : inter -> string
  val valeur_inter_dans_arbre : ab -> inter -> bool
end

(* MakeIntervalleArbre: Foncteur sur les intervalles d'arbre, prenant en parametre un intervalle pouvant ainsi définir le type d'élément sur les intervalles de l'arbre. Herite egalement du code sur un module d'arbre ayant comme élément un intervalle utilisant le type ordonnée*)
module MakeIntervalleArbre (O : IntervalleI) :
  IntervalleArbre with type element = O.element = struct
  (* InterOrdonne: Definition d'un module sur les intervalles incomplets pour le donner en parametre à notre foncteur d'arbre *)
  module InterOrdonne : TypeOrdonne with type t = O.inter = struct
    type t = O.inter

    let comp = O.comp
    let rand = O.random_intervalle
    let string_of_element = O.string_of_inter
    let next_element i = i
    let previous_element i = i
  end

  module ArbreInter = MakeArbre (InterOrdonne)
  include ArbreInter

  (* Definition des types et des façons de comparer les élements de ces types *)

  type element = O.element
  type inter = O.inter

  let compElement = O.compElement
  let inter = O.inter
  let random_intervalle = O.random_intervalle
  let bornemin = O.bornemin

  (* Fonction de base sur les arbres *)

  (* recup_inter: permet de récuperer l'intervalle d'un noeud *)
  let recup_inter = ArbreInter.recup_element

  (* Question 6 *)

  (* est_dans_arbre_intervalle: indique si l'élément e se trouve dans l'arbre *)
  let rec est_dans_arbre_intervalle e = function
    | Node (x, _, _, _) when O.est_dans_intervalle e x -> true
    | Node (x, _, ag, _) when compElement e (bornemin x) <= 0 ->
        est_dans_arbre_intervalle e ag
    | Node (_, _, _, ad) -> est_dans_arbre_intervalle e ad
    | _ -> false

  (* Fonctions permettant de gerer l'algorithme d'ajout et de retrait d'intervalle dans un arbre bicolore *)

  (* retire_list: retire les intervalles de la liste l de ab *)
  let retire_list ab l = if l <> [] then List.fold_right supprimer l ab else ab

  (* inter_non_disjoints: renvoie une liste contenant tous les intervalles de ab n'etant pas disjoints avec i *)
  let inter_non_disjoints i ab =
    let rec aux i acc = function
      | [] -> acc
      | Empty :: ts -> aux i acc ts
      | t :: ts ->
          let r, ag, ad = exploser t in
          if O.sont_disjoints r i then aux i acc (ag :: ad :: ts)
          else aux i (r :: acc) (ag :: ad :: ts)
    in
    aux i [] [ ab ]

  (* union_nondisjoints: réalise l'union entre deux intervalles i1 et i2 supposés non disjoints *)
  let union_nondisjoints i1 i2 =
    let i = O.union i1 i2 in
    match i with Either.Right i -> i | _ -> failwith "erreur"

  (* Question 7 *)

  (* ajout: ajoute i à l'arbre a *)
  let ajout i a =
    let l = inter_non_disjoints i a in
    let a = retire_list a l in
    inserer (List.fold_left union_nondisjoints i l) a

  (* retrait: retire l'intervalle i de a *)
  let retrait i a =
    let l = inter_non_disjoints i a in
    let a = retire_list a l in
    let l' = List.map ((Fun.flip O.difference) i) l in
    let l' = O.liste_intervalle_retrait l' in
    List.fold_right inserer l' a

  (* Fonctions ensemblistes de base sur les intervalles *)

  (* union: réalise l'union de a et b *)
  let union a b =
    let rec aux acc = function
      | [] -> acc
      | Empty :: ts -> aux acc ts
      | t :: ts ->
          let r, ag, ad = exploser t in
          aux (ajout r acc) (ag :: ad :: ts)
    in
    aux a [ b ]

  (* intersection: renvoie l'intersection entre a et b *)
  let intersection a b =
    let rec aux acc = function
      | Empty -> acc
      | b ->
          let r, ag, ad = exploser b in
          let acc' = if estDans r a then ajout r acc else acc in
          aux (aux acc' ag) ad
    in
    aux Empty b

  (* difference: renvoie la différence de a par b *)
  let difference a b =
    let rec aux acc = function
      | [] -> acc
      | Empty :: ts -> aux acc ts
      | t :: ts ->
          let r, ag, ad = exploser t in
          aux (retrait r acc) (ag :: ad :: ts)
    in
    aux a [ b ]

  (* Affichage des arbres *)

  (* string_of_inter: renvoie un string associé à l'intervalle *)
  let string_of_inter = O.string_of_inter

  (* to_string: transforme un arbre d'intervalles en string *)
  let rec to_string = function
    | Empty | VideNoir -> "Vide"
    | Node (r, _, ag, ad) ->
        "Node(" ^ string_of_inter r ^ ", " ^ to_string ag ^ ", " ^ to_string ad
        ^ ")"

  (* random_liste_intervalle: Création d'une liste aléatoire de k intervalles *)
  let random_liste_intervalle k =
    let rec aux k acc =
      match k with 0 -> acc | _ -> aux (k - 1) (O.random_intervalle 50 :: acc)
    in
    aux k []

  (* affiche_liste_inter: Affichage d'une liste d'intervalle *)
  let rec affiche_list_inter = function
    | [] -> ()
    | i :: ts ->
        Printf.printf "%s" (string_of_inter i);
        affiche_list_inter ts

  (* valeur_inter_dans_arbre: Indique si les éléments d'un intervalle i se trouvent dans l'arbre a *)
  let valeur_inter_dans_arbre a i =
    let rec aux acc min max =
      if compElement min max <= 0 then
        aux (acc && est_dans_arbre_intervalle min a) (O.next_element min) max
      else acc
    in
    aux true (O.borneminFerme i) (O.bornemaxFerme i)

  (* is_verified_all: Vérifie si la fonction f est vérifié pour tout element de la liste l associé à l'arbre a *)
  let is_verified_all l a f =
    let rec aux a f acc = function
      | [] -> acc
      | t :: ts -> aux a f (acc && f a t) ts
    in
    aux a f true l

  (* liste_vers_interAb: Transforme une liste d'intervalle l en arbre *)
  let liste_vers_interAb l = List.fold_left (Fun.flip ajout) Empty l

  (* liste_disjoints: Indique si les intervalles d'une liste d'éléments l sont disjoints un à un, en comparant le premier avec le suivant*)
  let liste_disjoints l =
    let rec aux acc previousI = function
      | [] -> acc
      | t :: ts -> aux (acc && O.sont_disjoints t previousI) t ts
    in
    match l with [] -> true | t :: ts -> aux true t ts

  (* est_dans_arbre_retrait: Indique si les éléments de la liste l sont dans a' et pas dans i' *)
  let est_dans_arbre_retrait l a' i' =
    let rec aux acc a' i' = function
      | [] -> acc
      | t :: ts when est_dans_arbre_intervalle t a' ->
          aux
            (acc
            && est_dans_arbre_intervalle t a'
            && not (O.est_dans_intervalle t i'))
            a' i' ts
      | _ :: ts -> aux acc a' i' ts
    in
    aux true a' i' l

  (* Question 8 *)

  (* valide_arbres_inter: Vérifie la validité d'un arbre d'intervalles aléatoire *)
  let valide_arbres_inter () =
    let l = random_liste_intervalle 5 in
    Printf.printf "\nListe aléatoire d'intervalles:";
    affiche_list_inter l;
    let a = liste_vers_interAb l in
    Printf.printf "\n\nArbre réalisé avec la liste:  %s\n" (to_string a);
    let b = is_verified_all l a valeur_inter_dans_arbre in
    Printf.printf "\nListe inclue dans l'arbre: %b\n" b;
    Printf.printf "\nEst Bicolore: %b\n" (est_bicolore a);
    Printf.printf "\nSont disjoints: %b\n"
      (liste_disjoints (arbre_vers_liste a));
    let i' = O.random_intervalle 50 in
    Printf.printf "\nIntervalle i': %s\n" (O.string_of_inter i');
    let a' = retrait i' a in
    Printf.printf "\nArbre avec retrait de i':  %s\n" (to_string a');
    Printf.printf
      "\nListe d'élément dans le nouvel arbre mais pas dans i' : %b\n"
      (est_dans_arbre_retrait (O.random_list_element 50) a' i');
    ()
end

(* TEST *)

module IntervalleArbreEntier = MakeIntervalleArbre (IntervalleEntier)
open IntervalleArbreEntier

(* let x = ajout (Option.get (inter 15 17 true true)) vide
   let x = ajout (Option.get (inter 5 9 false false)) x
   let x = ajout (Option.get (inter 100 125 true true)) x
   let x = ajout (Option.get (inter 0 4 true true)) x
   let x = ajout (Option.get (inter 50 50 true true)) x
   let x = ajout (Option.get (inter 126 28954 true true)) x
   let a = est_bicolore x;;

   to_string x

   let x = retrait (Option.get (inter 5 9 false false)) x;;

   to_string x

   let x = retrait (Option.get (inter 15 17 true true)) x;;

   to_string x

   let x = ajout (Option.get (inter 5 20 false true)) x;;

   to_string x

   let x = retrait (Option.get (inter 0 4 true true)) x
   let x = retrait (Option.get (inter 5 20 false true)) x;;

   to_string x

   let x = ajout (Option.get (inter 0 2 true false)) x
   let x = ajout (Option.get (inter 17 20 false true)) x;;

   to_string x

   let l = valide_arbres_inter ()
   let x = ajout (random_intervalle 5) vide;;

   to_string x

   let y = ajout (random_intervalle 5) x;;

   to_string y

   let z = ajout (random_intervalle 5) y;;

   to_string z

   let a = retrait (random_intervalle 5) z;;

   to_string a *)

let a = valide_arbres_inter ()
