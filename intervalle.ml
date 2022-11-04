(* TypeOrdonne: Interface pour définir les types éléments *)
module type TypeOrdonne = sig
  type t

  val comp : t -> t -> int
  val rand : int -> t
  val string_of_element : t -> string
  val next_element : t -> t
  val previous_element : t -> t
end

(* EntierOrdreNatuel: Exemple de type utilisant les entiers *)
module EntierOrdreNaturel : TypeOrdonne with type t = int = struct
  type t = int

  let comp = compare
  let rand = Random.int
  let string_of_element = string_of_int
  let next_element x = x + 1
  let previous_element x = x - 1
end

(* IntervalleI: Interface définissant les intervalles *)
module type IntervalleI = sig
  type element
  type inter

  val inter : element -> element -> bool -> bool -> inter option
  val vide : unit -> inter
  val est_dans_intervalle : element -> inter -> bool
  val comp : inter -> inter -> int
  val compElement : element -> element -> int
  val sont_disjoints : inter -> inter -> bool
  val union : inter -> inter -> (inter * inter, inter) Either.t
  val difference : inter -> inter -> (inter * inter, inter) Either.t
  val random_intervalle : int -> inter
  val valide_inter : unit -> unit
  val bornemin : inter -> element
  val bornemax : inter -> element
  val borneminFerme : inter -> element
  val bornemaxFerme : inter -> element
  val string_of_element : element -> string
  val string_of_inter : inter -> string
  val next_element : element -> element
  val random_list_element : int -> element list

  val liste_intervalle_retrait :
    (inter * inter, inter) Either.t list -> inter list
end

(* MakeIntervalle: Foncteur définissant les intervalles et prenant en parametre un TypeOrdonné servant à définir les éléments sur ces intervalles *)
module MakeIntervalle (O : TypeOrdonne) : IntervalleI with type element = O.t =
struct
  (* Question 1 *)

  (* 1 *)
  type element = O.t
  type inter = Vide | Inter of (element * element * bool * bool)

  let compElement = O.comp
  let ( $=$ ) x y = compElement x y = 0
  let ( $<$ ) x y = compElement x y < 0
  let ( $>$ ) x y = compElement x y > 0
  let rand = O.rand
  let string_of_element = O.string_of_element
  let next_element = O.next_element
  let vide () = Vide

  (* 2 *)

  (* Inter: Renvoie un intervalle valide. x et y sont respectivement les bornes mins et max, et bx et by indiquent la fermerture des bornes *)
  let inter x y bx by =
    if x $>$ y then None
    else if x > y then failwith "mauvaise valeur intervalle"
    else
      let i = Inter (x, y, bx, by) in
      Some i

  (* 3 *)

  (* est_dans_intervalle: Indique si e€i *)
  let est_dans_intervalle e i =
    match i with
    | Inter (x, y, _, _) when e $>$ x && e $<$ y -> true
    | Inter (x, y, bx, by) when (e $=$ x && bx) || (e $=$ y && by) -> true
    | _ -> false

  (* Question 2 *)

  (* comp: Compare deux intervalles, renvoie une valeur positive si i1 > i2, 0 si i1 = i2, négative sinon *)
  let comp i1 i2 =
    match (i1, i2) with
    | Vide, _ | _, Vide -> failwith "comparé au vide"
    | Inter (x1, _, _, _), Inter (x2, _, _, _) when x1 $<$ x2 -> -1
    | Inter (x1, _, _, _), Inter (x2, _, _, _) when x1 $>$ x2 -> 1
    | Inter (_, _, bx1, _), Inter (_, _, bx2, _) when bx2 < bx1 -> -1
    | Inter (_, _, bx1, _), Inter (_, _, bx2, _) when bx2 > bx1 -> 1
    | Inter (_, y1, _, _), Inter (_, y2, _, _) when y1 $<$ y2 -> -1
    | Inter (_, y1, _, _), Inter (_, y2, _, _) when y1 $>$ y2 -> 1
    | Inter (_, _, _, by1), Inter (_, _, _, by2) when by2 < by1 -> -1
    | Inter (_, _, _, by1), Inter (_, _, _, by2) when by2 > by1 -> 1
    | _ -> 0

  (* Question 3 *)

  (* sont_disjoints: Calcule si deux intervalles i1 et i2 sont disjoints *)
  let sont_disjoints i1 i2 =
    match (i1, i2) with
    | Inter (x, _, _, _), Inter (_, y, _, _) when x $>$ y -> true
    | Inter (_, y, _, _), Inter (x, _, _, _) when x $>$ y -> true
    | Inter (x, _, bx, _), Inter (_, y, _, by)
      when x $=$ y && (bx != by || (bx = by && bx = false)) ->
        true
    | Inter (_, y, _, by), Inter (x, _, bx, _)
      when x $=$ y && (bx != by || (bx = by && bx = false)) ->
        true
    | Vide, _ | _, Vide -> true
    | _ -> false

  (* Question 4 *)

  (* bornemin : Permet de récuperer la borne min d'un intervalle *)
  let bornemin = function Inter (x, _, bx, _) -> (x, bx) | _ -> failwith ""

  (* bornemax : Permet de récuperer la borne max d'un intervalle *)
  let bornemax = function Inter (_, y, _, by) -> (y, by) | _ -> failwith ""

  (* union: Calcule l'union de deux intervalles i1 et i2 *)
  let union i1 i2 =
    match (i1, i2) with
    | i1, Vide -> Either.right i1
    | Vide, i2 -> Either.right i2
    | Inter (x, y, bx, by), Inter (x2, y2, bx2, by2) when y $=$ x2 && by != bx2
      ->
        Either.right (Inter (x, y2, bx, by2))
    | Inter (x, y, bx, by), Inter (x2, y2, bx2, by2) when y2 $=$ x && by2 != bx
      ->
        Either.right (Inter (x2, y, bx2, by))
    | i1, i2 when not (sont_disjoints i1 i2) ->
        if comp i1 i2 >= 1 then
          let y, _ = bornemax i2 in
          let x', bx' = bornemin i2
          and y', by' =
            if est_dans_intervalle y i1 then bornemax i1 else bornemax i2
          in
          Either.right (Inter (x', y', bx', by'))
        else
          let y, _ = bornemax i2 in
          let x', bx' = bornemin i1
          and y', by' =
            if est_dans_intervalle y i1 then bornemax i1 else bornemax i2
          in
          Either.right (Inter (x', y', bx', by'))
    | i1, i2 when sont_disjoints i1 i2 ->
        if comp i1 i2 >= 1 then Either.left (i2, i1) else Either.left (i1, i2)
    | _ -> failwith ""

  (* difference: Renvoie la différence de i1 par i2 *)
  let difference i1 i2 =
    match (i1, i2) with
    | i1, Vide -> Either.right i1
    | Vide, _ -> Either.right Vide
    | i1, i2 when sont_disjoints i1 i2 -> Either.right i1
    | Inter (x, y, bx, by), Inter (x2, y2, bx2, by2)
      when (x2 $<$ x && y2 $>$ y)
           || x $=$ x2 && y $=$ y2
              && (bx = bx2 || bx = false)
              && (by = by2 || by = false)
           || (x $>$ x2 && y $=$ y2 && (by = by2 || by = false))
           || (x $=$ x2 && y $<$ y2 && (bx = bx2 || bx = false)) ->
        Either.right Vide
    | Inter (x, y, bx, by), Inter (x2, y2, bx2, by2)
      when (x $>$ x2 && y $>$ y2)
           || (x2 $=$ x && y $>$ y2 && (bx = bx2 || bx = false)) ->
        Either.right (Inter (y2, y, not by2, by))
    | Inter (x, y, bx, by), Inter (x2, y2, bx2, by2)
      when (x $<$ x2 && y $<$ y2)
           || (x2 $>$ x && y2 $=$ y && (by = by2 || by = false)) ->
        Either.right (Inter (x, x2, bx, not bx2))
    | Inter (x, y, bx, by), Inter (x2, y2, bx2, by2)
      when x2 $=$ x && y $=$ y2 && bx != bx2 && by != by2 && by = true
           && bx = true ->
        Either.left (Inter (x, x, true, true), Inter (y, y, true, true))
    | Inter (x, y, _, by), Inter (x2, y2, _, by2)
      when x2 $=$ x && y $=$ y2 && by != by2 ->
        Either.right (Inter (y, y, true, true))
    | Inter (x, y, bx, _), Inter (x2, y2, bx2, _)
      when x2 $=$ x && y $=$ y2 && bx != bx2 ->
        Either.right (Inter (x, x, true, true))
    | Inter (x, y, bx, by), Inter (x2, y2, bx2, by2)
      when x $=$ x2 && y $>$ y2 && bx != bx2 && bx = true ->
        Either.left (Inter (x, x, true, true), Inter (y2, y, not by2, by))
    | Inter (x, y, bx, by), Inter (x2, y2, bx2, by2)
      when x $<$ x2 && y $=$ y2 && by != by2 && by = true ->
        Either.left (Inter (x, x2, bx, not bx2), Inter (y, y, true, true))
    | Inter (x, y, bx, by), Inter (x2, y2, bx2, by2) when x2 $>$ x && y2 $<$ y
      ->
        Either.left (Inter (x, x2, bx, not bx2), Inter (y2, y, not by2, by))
    | _ -> Either.right i1

  (* Question 5 *)

  (* random_intervalle: Créer un intervalle aléatoire avec bornemax < value *)
  let random_intervalle value =
    let x = Random.init (Random.int 456874676) in
    let m = rand value and m' = rand value in
    let min, max = if m $<$ m' then (m, m') else (m', m) in
    if min $=$ max then Option.get (inter min max true true)
    else Option.get (inter min max (Random.bool x) (Random.bool x))

  (* is_included: Calcule l'inclusion via la différence entre les deux ensembles entre i1 et i2*)
  let is_included i1 i2 =
    Option.get (Either.find_right (difference i1 i2)) == Vide

  (* is_included_union: Calcule l'inclusion entre un ensemble i1 et un ensemble i4 = i2 U i3 *)
  let is_included_union i1 i2 i3 =
    match (i1, i2, i3) with
    | Inter (x, y, bx, by), Inter (x2, y2, bx2, by2), Inter (x3, y3, bx3, by3)
      ->
        (x $>$ x2 || (x $=$ x2 && bx <= bx2))
        && (y $<$ y2 || (y $=$ y2 && by <= by2))
        || (x $>$ x3 || (x $=$ x3 && bx <= bx3))
           && (y $<$ y3 || (y $=$ y3 && by <= by3))
    | _, _, _ -> false

  (* is_included_either: Calcule l'inclusion entre un ensemble i1 et i2, avec i2 du type Either.t *)
  let is_included_either i1 i2 =
    match i2 with
    | Either.Left (i3, i4) -> is_included_union i1 i3 i4
    | Either.Right i -> is_included i1 i

  (* is_included_either_2: Calcule l'inclusion entre un ensemble i4 et i2, avec i4 du type Either.t *)
  let is_included_either_2 i4 i1 =
    match i4 with
    | Either.Left (i2, i3) -> is_included i2 i1 && is_included i3 i1
    | Either.Right i -> is_included i i1

  (* string_of_inter: transforme un intervalle en string de la forme [ si l'intervalle est fermé à gauche, ] sinon + bornemin:bornemax + ] si l'intervalle est fermé à droite, [ sinon *)
  let string_of_inter = function
    | Inter (x, y, bx, by) ->
        (if bx then "[" else "]")
        ^ (string_of_element x ^ ";" ^ string_of_element y)
        ^ if by then "]" else "["
    | Vide -> "Vide"

  (* affiche_inter: Affiche à l'écran un intervalle i*)
  let affiche_inter i = Printf.printf "%s" (string_of_inter i)

  (* affiche_union: Affiche à l'écran une union d'intervalle si il y en a un, sinon un intervalle seul *)
  let affiche_union = function
    | Either.Left (i1, i2) ->
        affiche_inter i1;
        Printf.printf " U ";
        affiche_inter i2
    | Either.Right i -> affiche_inter i

  (* affiche_bool: Affiche un booléen b à l'écran *)
  let affiche_bool b =
    if b then Printf.printf "true" else Printf.printf "false";
    ()

  (* valide_diff: indique si les valeurs de i1 sont exclusivement soit dans i2 soit dans i4 *)
  let valide_diff i1 i2 i4 =
    let x = is_included_either_2 i4 i1 in
    match i4 with
    | Either.Left (i5, i6) ->
        sont_disjoints i5 i2 && sont_disjoints i6 i2 && x
        && is_included_either_2
             (difference (Option.get (Either.find_right (difference i1 i5))) i6)
             i2
    | Either.Right i ->
        sont_disjoints i i2 && x && is_included_either_2 (difference i1 i) i2

  (* valide_inter: Permet de tester la validité des intervalles *)
  let valide_inter () =
    let i1 = random_intervalle 200 and i2 = random_intervalle 100 in
    let i3 = union i1 i2 and i4 = difference i1 i2 in
    Printf.printf "\ni1: ";
    affiche_inter i1;
    Printf.printf "\ni2: ";
    affiche_inter i2;
    Printf.printf "\nUnion i1 et i2: ";
    affiche_union i3;
    Printf.printf "\nDifférence i1 et i2: ";
    affiche_union i4;
    Printf.printf "\nBool Union: ";
    affiche_bool (is_included_either i1 i3 && is_included_either i2 i3);
    Printf.printf "\nBool Difference: ";
    affiche_bool (valide_diff i1 i2 i4);
    Printf.printf "\n";
    ()

  (* Fonctions utiles pour les arbres d'intervalles *)

  (* bornemin: renvoie la borne min de l'intervalle, cette fois sans l'indication de fermeture *)
  let bornemin = function Inter (x, _, _, _) -> x | _ -> failwith "Vide"

  (* bornemax: renvoie la borne max de l'intervalle, cette fois sans l'indication de fermeture *)
  let bornemax = function Inter (_, y, _, _) -> y | _ -> failwith "Vide"

  (* borneminFerme: renvoie la borne min de l'intervalle si celle ci est fermée, sinon le prochain élément de la borne min *)
  let borneminFerme = function
    | Inter (x, _, true, _) -> x
    | Inter (x, _, false, _) -> O.next_element x
    | _ -> failwith "Vide"

  (* bornemaxFerme: renvoie la borne max de l'intervalle si celle ci est fermée, sinon le précédent élément de la borne max *)
  let bornemaxFerme = function
    | Inter (_, y, _, true) -> y
    | Inter (_, y, _, false) -> O.previous_element y
    | _ -> failwith "Vide"

  (* liste_intervalle_retrait: Fonction transformant une liste d'intervalles Either.t l en liste classique d'intervalles sans Vide *)
  let liste_intervalle_retrait l =
    let rec aux acc = function
      | [] -> acc
      | Either.Right Vide :: ts -> aux acc ts
      | Either.Right i :: ts -> aux (i :: acc) ts
      | Either.Left (i1, i2) :: ts -> aux (i1 :: i2 :: acc) ts
    in
    aux [] l

  (* random_list_element: Fonction renvoyant une liste de int élément aléatoire *)
  let random_list_element int =
    let rec aux acc = function
      | 0 -> acc
      | t -> aux (O.rand (Random.int 99999) :: acc) (t - 1)
    in
    aux [] int
end

(* IntervalleEntier: Intervalle sur les entiers *)
module IntervalleEntier = MakeIntervalle (EntierOrdreNaturel)
open IntervalleEntier

let x = valide_inter ()
