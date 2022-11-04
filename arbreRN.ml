open Intervalle

(* Arbre: Interface définissant des arbres d'éléments quelconques *)
module type Arbre = sig
  type elementA
  type couleur
  type ab = Empty | VideNoir | Node of elementA * couleur * ab * ab

  val vide : ab
  val recup_element : ab -> elementA
  val estVide : ab -> bool
  val estDans : elementA -> ab -> bool
  val inserer : elementA -> ab -> ab
  val supprimer : elementA -> ab -> ab
  val supprimerMax : ab -> elementA * ab
  val differenceSym : ab -> ab -> ab
  val arbre_vers_liste : ab -> elementA list
  val liste_vers_arbre : elementA list -> ab
  val est_inclus_dans : ab -> ab -> bool
  val card : ab -> int
  val est_bicolore : ab -> bool
  val recolorerRacineNoire : ab -> ab
  val exploser : ab -> elementA * ab * ab
  val est_egal : ab -> ab -> bool
end

(* MakeArbre: Foncteur définissant des arbres d'élements de TypeOrdonné *)
module MakeArbre (O : TypeOrdonne) : Arbre with type elementA = O.t = struct
  type elementA = O.t

  (* comp: Comparaison sur les éléments de l'arbre *)
  let comp = O.comp

  (* Défintion des opérations de comparaison sur les éléments de l'arbre *)
  let ( $=$ ) x y = comp x y = 0
  let ( $<$ ) x y = comp x y < 0
  let ( $>$ ) x y = comp x y > 0

  (* Type de l'arbre *)
  type couleur = Noir | Rouge | DoubleNoir
  type ab = Empty | VideNoir | Node of elementA * couleur * ab * ab

  let vide = Empty

  (* estVide: Indique si un arbre est vide *)
  let estVide = function Empty -> true | _ -> false

  (* recup_element: Permet de récupérer un élément de l'arbre *)
  let recup_element = function
    | Node (r, _, _, _) -> r
    | _ -> failwith "erreur pas d'element"

  (* estDans: Indique si l'élément e se trouve dans l'arbre *)
  let rec estDans e = function
    | Node (x, _, _, _) when e $=$ x -> true
    | Node (x, _, ag, _) when e $<$ x -> estDans e ag
    | Node (_, _, _, ad) -> estDans e ad
    | _ -> false

  (* recolorerRacineNoire: Change la racine de l'arbre en noir, peu importe sa couleur de base *)
  let recolorerRacineNoire = function
    | Node (r, _, ag, ad) -> Node (r, Noir, ag, ad)
    | Empty -> Empty
    | VideNoir -> failwith "pas bicolore"

  (* racineRouge: Indique si la racine est rouge *)
  let racineRouge = function Node (_, Rouge, _, _) -> true | _ -> false

  (* a_un_fils_rouge: Indique si le noeud possede un fils rouge *)
  let a_un_fils_rouge = function
    | Node (_, _, ag, ad) -> racineRouge ag || racineRouge ad
    | _ -> false

  (* rotation_gauche: Réalise une rotation gauche du noeud *)
  let rotation_gauche = function
    | Node (m, cM, a1, Node (n, cN, a2, a3)) ->
        Node (n, cN, Node (m, cM, a1, a2), a3)
    | _ -> failwith "Mauvais arbre , pas de rotation gauche"

  (* rotation_droite: Réalise une rotation droite du noeud *)
  let rotation_droite = function
    | Node (n, c, Node (m, c1, a1, a2), a3) ->
        Node (m, c1, a1, Node (n, c, a2, a3))
    | _ -> failwith "Mauvais arbre"

  (* equilibrer: Equilibre l'arbre pour le rendre bicolore apres une insertion *)
  let rec equilibrer = function
    | Node (g, Noir, (Node (_, Rouge, _, _) as p), (Node (_, Rouge, _, _) as f))
      when a_un_fils_rouge p || a_un_fils_rouge f ->
        Node (g, Rouge, recolorerRacineNoire p, recolorerRacineNoire f)
    | Node (g, Noir, (Node (_, Rouge, Node (_, Rouge, _, _), _) as p), f) ->
        rotation_droite (Node (g, Rouge, recolorerRacineNoire p, f))
    | Node (g, Noir, (Node (_, Rouge, _, Node (_, Rouge, _, _)) as p), f) ->
        equilibrer (Node (g, Noir, rotation_gauche p, f))
    | Node (g, Noir, f, (Node (_, Rouge, Node (_, Rouge, _, _), _) as p)) ->
        equilibrer (Node (g, Noir, f, rotation_droite p))
    | Node (g, Noir, f, (Node (_, Rouge, _, Node (_, Rouge, _, _)) as p)) ->
        rotation_gauche (Node (g, Rouge, f, recolorerRacineNoire p))
    | a -> a

  (* inserer: Insere un élément x dans l'arbre t *)
  let inserer x t =
    let rec aux = function
      | Empty -> Node (x, Rouge, Empty, Empty)
      | Node (r, c, ag, ad) when x $<$ r -> equilibrer (Node (r, c, aux ag, ad))
      | Node (r, c, ag, ad) when x $>$ r -> equilibrer (Node (r, c, ag, aux ad))
      | a -> a
    in
    recolorerRacineNoire (aux t)

  (* diminuer_poids: Diminue le "poids" d'un noeud, avec DoubleNoir > Noir > Rouge *)
  let diminuer_poids = function
    | Node (x, DoubleNoir, ag, ad) -> Node (x, Noir, ag, ad)
    | Node (x, Noir, ag, ad) -> Node (x, Rouge, ag, ad)
    | VideNoir -> Empty
    | a -> a

  (* augmenter_couleur: Augmente une couleur avec Rouge < Noir < DoubleNoir *)
  let augmenter_couleur = function Rouge -> Noir | Noir -> DoubleNoir | a -> a

  (* estProblematique: Indique si un noeud est problématique, c'est à dire si il vaut VideNoir ou si il possede la couleur DoubleNoir *)
  let estProblematique = function
    | VideNoir | Node (_, DoubleNoir, _, _) -> true
    | _ -> false

  (* noirSansFilsRouge: Indique si le noeud est noir sans fils rouge *)
  let noirSansFilsRouge = function
    | Node
        (_, Noir, (Node (_, Noir, _, _) | Empty), (Node (_, Noir, _, _) | Empty))
      ->
        true
    | _ -> false

  (* eq_supp: Equilibre un arbre apres une suppression *)
  let rec eq_supp = function
    | Node (p, c, x, f)
      when (estProblematique x && noirSansFilsRouge f)
           || (estProblematique f && noirSansFilsRouge x) ->
        Node (p, augmenter_couleur c, diminuer_poids x, diminuer_poids f)
    | Node (p, c, x, Node (f, Noir, a3, (Node (_, Rouge, _, _) as d)))
      when estProblematique x ->
        Node (f, c, Node (p, Noir, diminuer_poids x, a3), recolorerRacineNoire d)
    | Node (p, c, x, Node (f, Noir, Node (g, Rouge, a3, a4), a5))
      when estProblematique x ->
        eq_supp (Node (p, c, x, Node (g, Noir, a3, Node (f, Rouge, a4, a5))))
    | Node (p, Noir, x, Node (f, Rouge, a1, a2)) when estProblematique x ->
        Node (f, Noir, eq_supp (Node (p, Rouge, x, a1)), a2)
    | Node (p, c, Node (f, Noir, Node (g, Rouge, a3, a4), a2), x)
      when estProblematique x ->
        Node (f, c, Node (g, Noir, a3, a4), Node (p, Noir, a2, diminuer_poids x))
    | Node
        (p, c, Node (f, Noir, Node (g, c2, a3, a4), Node (d, Rouge, a1, a2)), x)
      when estProblematique x ->
        eq_supp
          (Node
             ( p,
               c,
               Node (d, Noir, Node (f, Rouge, Node (g, c2, a3, a4), a1), a2),
               x ))
    | Node (p, Noir, Node (f, Rouge, a1, a2), x) when estProblematique x ->
        Node (f, Noir, a1, eq_supp (Node (p, Rouge, a2, x)))
    | a -> a

  (* stabiliser: Permet de transformer des noeuds servant pour la suppression en noeud "classique" *)
  let stabiliser = function
    | VideNoir -> Empty
    | Node (r, DoubleNoir, ag, ad) -> Node (r, Noir, ag, ad)
    | a -> a

  (* supprimerMax: Supprime le max de l'arbre *)
  let rec supprimerMax = function
    | Node (r, Rouge, Empty, Empty) -> (r, Empty)
    | Node (r, Noir, Node (r', Rouge, Empty, Empty), Empty) ->
        (r, Node (r', Noir, Empty, Empty))
    | Node (r, Noir, Empty, Empty) -> (r, VideNoir)
    | Node (r, c, ag, ad) ->
        let m, ad' = supprimerMax ad in
        (m, eq_supp (Node (r, c, ag, ad')))
    | _ -> failwith ""

  (* supprimer_racine: Supprime la racine de l'arbre *)
  let supprimer_racine = function
    | Node (_, Rouge, Empty, Empty) -> Empty
    | Node (_, Noir, Empty, Node (r', Rouge, Empty, Empty)) ->
        Node (r', Noir, Empty, Empty)
    | Node (_, Noir, Empty, Empty) -> VideNoir
    | Node (_, c, ag, ad) ->
        let m, ag' = supprimerMax ag in
        eq_supp (Node (m, c, ag', ad))
    | _ -> failwith ""

  (* supprimer: Suppime un élément x de l'arbre a *)
  let supprimer x a =
    let rec aux = function
      | Empty -> Empty
      | Node (r, c, ag, ad) when x $<$ r -> eq_supp (Node (r, c, aux ag, ad))
      | Node (r, c, ag, ad) when x $>$ r -> eq_supp (Node (r, c, ag, aux ad))
      | a -> supprimer_racine a
    in
    stabiliser (aux a)

  (* exploser: Renvoie un couple avec la racine, l'arbre gauche recolorer en noir et l'arbre droit recolorer en noir *)
  let exploser = function
    | Node (r, _, ag, ad) ->
        (r, recolorerRacineNoire ag, recolorerRacineNoire ad)
    | _ -> failwith "probleme exploser"

  (* Fonction ensembliste de base sur les arbres *)
  (* union: renvoie l'union de a et b *)
  let union a b =
    let rec aux acc = function
      | [] -> acc
      | Empty :: ts -> aux acc ts
      | t :: ts ->
          let r, ag, ad = exploser t in
          aux (inserer r acc) (ag :: ad :: ts)
    in
    aux a [ b ]

  (* difference: renvoie la différence de a par b *)
  let difference a b =
    let rec aux acc = function
      | [] -> acc
      | Empty :: ts -> aux acc ts
      | t :: ts ->
          let r, ag, ad = exploser t in
          aux (supprimer r acc) (ag :: ad :: ts)
    in
    aux a [ b ]

  (* differenceSym: calcule la difference symétrique de a et b *)
  let differenceSym a b = union (difference a b) (difference b a)

  (* liste_vers_arbre: Transforme une liste en arbre *)
  let liste_vers_arbre l = List.fold_left (Fun.flip inserer) Empty l

  (* arbre_vers_liste: transforme un arbre en liste *)
  let rec arbre_vers_liste = function
    | Empty -> []
    | Node (r, _, ag, ad) -> arbre_vers_liste ag @ [ r ] @ arbre_vers_liste ad
    | VideNoir -> failwith "pas bicolore"

  (* est_inclus_dans: Indique si un arbre e1 est inclus dans un arbre e2 *)
  let rec est_inclus_dans e1 e2 =
    match e1 with
    | Empty -> true
    | _ ->
        let r, ag, ad = exploser e1 in
        estDans r e2 && est_inclus_dans ag e2 && est_inclus_dans ad e2

  (* est_egal: Indique si e1 est égal à e2 *)
  let est_egal e1 e2 = est_inclus_dans e1 e2 && est_inclus_dans e2 e1

  (* card: Renvoie le cardinal de l'arbre ab*)
  let card ab =
    let rec aux cpt = function
      | [] -> cpt
      | Empty :: xs -> aux cpt xs
      | Node (_, _, ag, ad) :: xs -> aux (cpt + 1) (ag :: ad :: xs)
      | VideNoir :: _ -> failwith "pas bicolore"
    in
    aux 0 [ ab ]

  (* Fonctions permettant de savoir si un arbre est bicolore ou non *)

  (* estDeRecherche: indique si l'arbre t est de recherche ou non *)
  let estDeRecherche t =
    let rec aux t =
      match t with
      | Empty -> failwith "arbre vide"
      | VideNoir -> failwith "arbre vide"
      | Node (r, _, Empty, Empty) -> (true, r, r)
      | Node (r, _, Empty, ad) ->
          let estDeRechD, valg, vald = aux ad in
          (estDeRechD && valg $>$ r, r, vald)
      | Node (r, _, ag, Empty) ->
          let estDeRechG, valg, vald = aux ag in
          (estDeRechG && vald $<$ r, valg, r)
      | Node (r, _, ag, ad) ->
          let estDeRechD, valgD, valdD = aux ad
          and estDeRechG, valgG, valdG = aux ag in
          (estDeRechD && estDeRechG && valgD $>$ r && valdG $<$ r, valgG, valdD)
    in
    match t with
    | Empty -> true
    | _ ->
        let res, _, _ = aux t in
        res

  (* pasDeuxRougesDeSuite: indique si il n'y a pas deux rouges de suite dans l'arbre t *)
  let pasDeuxRougesDeSuite t =
    let rec aux = function
      | [] -> true
      | (Rouge, Node (_, Rouge, _, _)) :: _ -> false
      | (_, Node (_, c, ag, ad)) :: xs -> aux ((c, ag) :: (c, ad) :: xs)
      | (_, Empty) :: xs -> aux xs
      | _ -> failwith "pas bicolore"
    in
    match t with
    | Empty -> true
    | Node (_, c, ag, ad) -> aux [ (c, ag); (c, ad) ]
    | VideNoir -> failwith "pas bicolore"

  (* racineNoire: indique si l'arbre possede une racine noire *)
  let racineNoire = function Node (_, Noir, _, _) -> true | _ -> false

  (* memesHauteursNoires: indique si tous les chemins menant de la racine jusqu'à un morceau extérieur de l'arbre (un noeud Vide) comportent le meme nombre de noeuds Noirs *)
  let memesHauteursNoires t =
    let rec aux = function
      | Empty -> (true, 0)
      | Node (_, c, ag, ad) -> (
          let memesHNG, hnG = aux ag and memesHND, hnD = aux ad in
          ( memesHNG && memesHND && hnG = hnD,
            match c with
            | Noir -> hnG + 1
            | Rouge -> hnG
            | DoubleNoir -> failwith "mauvaise couleur" ))
      | VideNoir -> failwith "pas bicolore"
    in
    fst (aux t)

  (* noeudsRougesOuNoirs: indique si tous les noeuds sont rouges ou noirs *)
  let rec noeudsRougesOuNoirs = function
    | Empty -> true
    | Node (_, couleur, ag, ad) when couleur = Rouge || couleur = Noir ->
        noeudsRougesOuNoirs ag && noeudsRougesOuNoirs ad
    | _ -> false

  (* est_bicolore: indique si l'arbre t est bicolore *)
  let est_bicolore t =
    estDeRecherche t
    && (racineNoire t || estVide t)
    && pasDeuxRougesDeSuite t && noeudsRougesOuNoirs t && memesHauteursNoires t
end
