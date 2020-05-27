(** Types *)
type resultat =
  | RInitial
  | RVide
  | RChaine of string
  | REntier of int
  | RFlottant of float
  | Erreur of erreur

and erreur =
  |Mauvais_indice of (int * int)
  |Cycle_detecte
  |Argument_BinOp_invalide
  |Argument_invalide

type expr =
  | Vide
  | Chaine of string
  | Entier of int
  | Flottant of float
  | Case of int * int
  | Unaire of op_unaire
  | Binaire of op_binaire
  | Reduction of op_reduction


and op_unaire = {app1 : resultat -> resultat; operande : expr}
and op_binaire = {app2 : resultat -> resultat -> resultat; gauche : expr; droite : expr}
and op_reduction = {app : resultat -> resultat -> resultat; init : resultat; case_debut : int * int; case_fin : int * int}





type grille = expr array array

(** Fonctions *)

exception Pas_encore_implemente of string
let cree_grille i j =
  let m = Array.make_matrix i j Vide in
  m

let rec expr_to_string g e =
  match e with
  |Vide -> ""
  |Chaine (s) -> s
  |Entier (n) -> string_of_int n
  |Flottant (f) -> string_of_float f
  |Case (n, m) -> "@(" ^ (string_of_int n) ^ "," ^ (string_of_int m) ^ ")"
  |Unaire (u) -> "app1 (" ^ expr_to_string g u.operande ^ ")"
  |Binaire (b) -> "app2 ()" ^ expr_to_string g b.gauche ^ ", " ^ expr_to_string g b.droite ^ ")"
  |Reduction (r) -> (match (r.case_debut, r.case_fin) with
      |((x, y),(xe, ye)) -> let tmp = ref "app (" in
        for i = (min x xe) to (max x xe) do
          for j = (min y ye) to (max y ye) do
            tmp := !tmp ^ expr_to_string g g.(i).(j) ^ ", "
          done
        done;
        tmp := !tmp ^ ")";
        !tmp)

let affiche_grille g =
  for i = 0 to Array.length(g) - 1 do
    for j = 0 to Array.length(g.(0)) -1  do
      if j = (Array.length(g.(0)) - 1) then
        Format.printf "|%12s|\n" (expr_to_string g g.(i).(j))
      else
        Format.printf "|%12s" (expr_to_string g g.(i).(j))
    done
  done

let cycle g e =
  let rec atteignable ex l =
    match ex with
    |Vide -> false
    |Chaine _ -> false
    |Entier _ -> false
    |Flottant _ -> false
    |Case (x, y) -> if List.mem (Case (x, y)) l then
        true
      else
        atteignable g.(x).(y) ((Case (x, y))::l)
    |Unaire (u) -> atteignable u.operande l
    |Binaire (b) -> (atteignable b.gauche l) && (atteignable b.droite l)
    |Reduction (r) -> (match (r.case_debut, r.case_fin) with
        |((x, y),(xe, ye)) -> let tmp = ref false in
          for i = (min x xe) to (max x xe) do
            for j = (min y ye) to (max y ye) do
              if atteignable g.(i).(j) l then tmp := true
            done
          done;
          !tmp)
  in
  atteignable e []

let rec eval_expr g e =
  match e with
  |Vide -> RVide
  |Chaine (s)-> RChaine (s)
  |Entier (n)-> REntier (n)
  |Flottant (f)-> RFlottant (f)
  |Case (x, y) -> if ((x >= Array.length g) || (y >= Array.length g.(0)) || y < 0 || x < 0) then
      Erreur (Mauvais_indice (x, y))
    else
    if cycle g e then
      Erreur Cycle_detecte
    else
      eval_expr g g.(x).(y)
  (*  |Unaire (u) -> (match eval_expr g u.operande with
      |RVide -> RVide
      |RChaine (s) -> u.app1 (RChaine (s))
      |REntier (n) -> u.app1 (REntier (n))
      |RFlottant (f) -> u.app1 (RFlottant (f))
      |Erreur (e) -> Erreur (e))
      |Binaire (b) -> (match (eval_expr g b.gauche, eval_expr g b.droite) with
      |(RVide,RVide) -> RVide
      |(RChaine (s1), RChaine (s2)) -> b.app2 (RChaine (s1)) (RChaine (s2))
      |(REntier (n1), REntier (n2)) -> b.app2 (REntier (n1)) (REntier (n2))
      |(RFlottant (f1), RFlottant (f2)) -> b.app2 (RFlottant (f1)) (RFlottant (f2))
      |_ -> Erreur Argument_BinOp_invalide) *)
  |Unaire u -> u.app1 (eval_expr g u.operande)
  |Binaire b -> b.app2 (eval_expr g b.gauche) (eval_expr g b.droite)
  |Reduction (r) ->
    (match (r.case_debut, r.case_fin) with
     |((x, y),(xe, ye)) -> let tmp = ref r.init in
       for i = (min x xe) to (max x xe) do
         for j = (min y ye) to (max y ye) do
           tmp := r.app !tmp (eval_expr g g.(i).(j))
         done
       done;
       !tmp)





let eval_grille g =
  let m = Array.make_matrix (Array.length g) (Array.length g.(0)) false in
  let res = Array.make_matrix (Array.length g) (Array.length g.(0)) RInitial in
  let rec eval_expr_memo e =
    match e with
    |Vide -> RVide
    |Chaine (s)-> RChaine (s)
    |Entier (n)-> REntier (n)
    |Flottant (f)-> RFlottant (f)
    |Case (x, y) ->
      if ((x >= Array.length g) || (y >= Array.length g.(0)) || y < 0 || x < 0) then
        Erreur (Mauvais_indice (x, y))
      else
      if cycle g e then
        Erreur Cycle_detecte
      else
      if res.(x).(y) != RInitial then res.(x).(y)
      else
        let r = eval_expr_memo g.(x).(y) in
        res.(x).(y) <- r;
        r
    (*    |Unaire (u) -> (match eval_expr_memo u.operande with
          |RVide -> RVide
          |RChaine (s) -> u.app1 (RChaine (s))
          |REntier (n) -> u.app1 (REntier (n))
          |RFlottant (f) -> u.app1 (RFlottant (f))
          |Erreur (e) -> Erreur (e))
          |Binaire (b) -> (match (eval_expr_memo b.gauche, eval_expr_memo b.droite) with
          |(RVide,RVide) -> RVide
          |(RChaine (s1), RChaine (s2)) -> b.app2 (RChaine (s1)) (RChaine (s2))
          |(REntier (n1), REntier (n2)) -> b.app2 (REntier (n1)) (REntier (n2))
          |(RFlottant (f1), RFlottant (f2)) -> b.app2 (RFlottant (f1)) (RFlottant (f2))
          |_ -> Erreur Argument_BinOp_invalide)   *)
    |Unaire u -> u.app1 (eval_expr_memo u.operande)
    |Binaire b -> b.app2 (eval_expr_memo b.gauche) (eval_expr_memo b.droite)
    |Reduction (r) ->
      (match (r.case_debut, r.case_fin) with
       |((x, y),(xe, ye)) -> let tmp = ref r.init in
         for i = (min x xe) to (max x xe) do
           for j = (min y ye) to (max y ye) do
             tmp := r.app !tmp (eval_expr_memo g.(i).(j))
           done
         done;
         !tmp)
  in
  for i = 0 to Array.length(g) - 1 do
    for j = 0 to Array.length(g.(0)) -1  do
      if m.(i).(j) then ()
      else
        res.(i).(j) <- eval_expr_memo g.(i).(j);
      m.(i).(j) <- true
    done
  done;
  res


let affiche_grille_resultat g =
  let res_to_string e =
    match e with
    |RInitial -> ""
    |RVide -> ""
    |RChaine (s) -> s
    |REntier (n) -> string_of_int n
    |RFlottant (f) -> string_of_float f
    |Erreur _ -> "erreur"
  in
  for i = 0 to Array.length(g) - 1 do
    for j = 0 to Array.length(g.(0)) -1  do
      if j = (Array.length(g.(0)) - 1) then
        Format.printf "|%12s|\n" (res_to_string g.(i).(j))
      else
        Format.printf "|%12s" (res_to_string g.(i).(j))
    done
  done




let rec abs g e =
  let abs_gen a =
    match a with
    |REntier (n) -> let absol a =
                      if a < 0 then (-a)
                      else a
      in
      REntier (absol n)
    |RFlottant (f) -> RFlottant (abs_float f)
    |_ -> Erreur Argument_invalide
  in
  match e with
  |Case _ -> (match  (eval_expr g e) with
      |RFlottant (f) -> abs g (Flottant (f))
      |REntier (n) -> abs g (Entier (n))
      |RChaine (s) -> abs g (Chaine (s))
      |_ -> abs g Vide)
  |_ -> Unaire {app1 = abs_gen; operande = e}

let rec add g e d =
  let add_mixte g d =
    match (g, d) with
    |(RFlottant (f), REntier (n)) -> RFlottant (f +. float_of_int n)
    |(REntier (n), RFlottant (f)) -> RFlottant (float_of_int n +. f)
    |(REntier (n), REntier (m)) -> REntier (n + m)
    |(RFlottant (f1), RFlottant (f2)) -> RFlottant (f1 +. f2)
    |_ -> Erreur Argument_invalide
  in
  match (e, d) with
  |(Case _, _) ->( match (eval_expr g e) with
      |RFlottant (f) -> add g (Flottant f) d
      |REntier (n) -> add g (Entier n) d
      |RChaine (s) -> add g (Chaine s) d
      |_ -> add g Vide d)
  |(_, Case _) -> (match (eval_expr g d) with
      |RFlottant (f) -> add g e (Flottant f)
      |REntier (n) -> add g e (Entier n)
      |RChaine (s) -> add g e (Chaine s)
      |_ -> add g e Vide)
  |(_, _) -> Binaire {app2 = add_mixte; gauche = e; droite = d}


let somme g d f =
  let (x, y) = d in
  let (x2, y2) = f in
  match (add g g.(x).(y) g.(x2).(y2)) with
  |Binaire b -> Reduction {app = b.app2; init = REntier 0; case_debut = (x, y); case_fin = (x2, y2)}
  |_ -> assert false





let () =
  let g = cree_grille 3 3 in
  g.(0).(0) <- Entier 1;
  g.(0).(1) <- Case (0, 0);
  g.(1).(0) <- Case (1, 1);
  g.(1).(1) <- Case (1, 0);
  affiche_grille g;
  print_string (string_of_bool (cycle g (Case (1, 0))));
  print_newline ();
  print_string (string_of_bool (cycle g (Case (0, 0))));
  print_newline ();
  g.(1).(1) <- Case (0, 1);
  g.(0).(1) <- Case (1, 0);
  g.(0).(2) <- Case (2, 1);
  g.(2).(0) <- Entier 5;
  g.(1).(2) <- Entier 3;
  g.(2).(2) <- add g (Case (1, 1)) (Case (1, 2));
  g.(2).(1) <- Case (0, 0);
  affiche_grille g;
  print_newline ();
  let r = eval_grille g in
  affiche_grille_resultat r;
  print_newline ();
  g.(2).(2) <- add g (Case (0, 0)) (Case (1, 2));
  affiche_grille g;
  print_string (string_of_bool (cycle g (Case (1, 0))));
  print_newline ();
  let r2 = eval_grille g in
  affiche_grille_resultat r2
