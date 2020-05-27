type erreur =
  | Cycle_detecte
  | Mauvais_indice of (int * int)
  | Div_by_zero
  | Mauvais_arguments
  | Mal_evalue
  | Syntax of string

type resultat =
  | RVide
  | RChaine of string
  | REntier of int
  | RFlottant of float
  | Erreur of erreur

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

and op_binaire = {
  app2 : resultat -> resultat -> resultat;
  gauche : expr;
  droite : expr;
}

and op_reduction = {
  app : resultat -> resultat -> resultat;
  init : resultat;
  case_debut : int * int;
  case_fin : int * int;
}

let pp_expr fmt (expr : expr) =
  let pp = Format.fprintf in
  match expr with
  | Vide ->
      pp fmt "%8s" "."
  | Chaine s ->
      if String.length s > 8 then pp fmt "str %8s" (String.sub s 0 8)
      else pp fmt "str %8s" s
  | Entier i ->
      pp fmt "int %8d" i
  | Flottant f ->
      pp fmt "%6.2f" f
  | Case (i, j) ->
      pp fmt "c(%2d,%2d)" i j
  | Unaire _ ->
      pp fmt "una"
  | Binaire _ ->
      pp fmt "bin"
  | Reduction _ ->
      pp fmt "red"

let pp_err fmt (erreur : erreur) =
  match erreur with
  | Cycle_detecte ->
      Format.fprintf fmt "%8s" "cycle"
  | Mauvais_indice (i, j) ->
      Format.fprintf fmt "%8s" (Format.asprintf "ind(%d,%d)" i j)
  | Div_by_zero ->
      Format.fprintf fmt "%8s" "div0"
  | Mauvais_arguments ->
      Format.fprintf fmt "%8s" "arg_inv"
  | Mal_evalue ->
      Format.fprintf fmt "%8s" "eval_err"
  | Syntax msg ->
      Format.fprintf fmt "%8s" "syntax"

let pp_resultat fmt (res : resultat) =
  let pp = Format.fprintf in
  match res with
  | RVide ->
      pp fmt "%8s" "."
  | RChaine s ->
      if String.length s > 8 then pp fmt "%8s" (String.sub s 0 8)
      else pp fmt "%8s" s
  | REntier i ->
      pp fmt "%8d" i
  | RFlottant f ->
      pp fmt "%6.2f" f
  | Erreur err ->
      pp_err fmt err

let pp_expr_grid fmt grid =
  Array.iter
    (fun lines ->
      Array.iter (fun r -> Format.fprintf fmt "%a " pp_expr r) lines ;
      Format.fprintf fmt "@\n")
    grid

let pp_res_grid fmt grid =
  Array.iter
    (fun lines ->
      Array.iter (fun r -> Format.fprintf fmt "%a " pp_resultat r) lines ;
      Format.fprintf fmt "@\n")
    grid

let ( -- ) i j = List.init (j - i + 1) (fun x -> x + i)

let int_to_letter j =
  let ltval = j mod 26 in
  let nb = (j - ltval) / 26 in
  let nb = if nb = 0 then "" else string_of_int nb in
  let lt = char_of_int (int_of_char 'A' + ltval) in
  Format.sprintf "%c%s" lt nb

let rec product a b =
  match a with
  | [] ->
      []
  | hd :: tl ->
      List.map (fun x -> (hd, x)) b @ product tl b

(** Fonctions *)

let cree_grille longueur largeur = Array.make_matrix longueur largeur

let coords_of_plage (i, j) (i', j') =
  let l = if i < i' then i -- i' else i' -- i in
  let j = if j < j' then j -- j' else j' -- j in
  product l j

let cases_of_plage (i, j) (i', j') =
  coords_of_plage (i, j) (i', j') |> List.map (fun (i, j) -> Case (i, j))

module type CELL = sig
  type t

  val get_expr : t -> expr
end

module CaseSet = Set.Make (struct
  type t = int * int

  let compare = compare
end)

module type T = sig
  type grille

  val eval : grille -> int -> int -> resultat
end

type grille = expr array array

(** Utils *)

let find_or_compute h v f =
  try Hashtbl.find h v
  with Not_found ->
    let result = f () in
    Hashtbl.add h v result ; result

let cycle grid =
  let h = Hashtbl.create 18 in
  let rec loop visited (expr : expr) =
    match expr with
    | Vide | Entier _ | Flottant _ | Chaine _ ->
        false
    | Case (i, j) -> (
        CaseSet.mem (i, j) visited
        || find_or_compute h (i, j)
           @@ fun () ->
           try loop (CaseSet.add (i, j) visited) grid.(i).(j)
           with Invalid_argument _ -> false
        (* laisser eval gérer ça *) )
    | Unaire {operande; _} ->
        loop visited operande
    | Binaire {gauche; droite; _} ->
        loop visited gauche || loop visited droite
    | Reduction {case_debut; case_fin; _} ->
        cases_of_plage case_debut case_fin
        |> List.fold_left (fun b c -> b || loop visited c) false
  in
  fun i j ->
    try Hashtbl.find h (i, j)
    with Not_found -> (
      find_or_compute h (i, j)
      @@ fun () ->
      try loop CaseSet.empty grid.(i).(j) with Invalid_argument _ -> false )

let eval grid =
  let h = Hashtbl.create 18 in
  let cycle = cycle grid in
  let rec eval expr =
    let eval_unaire {app1; operande} = app1 (eval operande) in
    let eval_binaire {app2; gauche; droite} =
      app2 (eval gauche) (eval droite)
    in
    let eval_reduc {app; init; case_debut; case_fin} =
      cases_of_plage case_debut case_fin
      |> List.fold_left (fun acc c -> app acc (eval c)) init
    in
    match expr with
    | Vide ->
        RVide
    | Entier i ->
        REntier i
    | Flottant f ->
        RFlottant f
    | Chaine s ->
        RChaine s
    | Case (i, j) -> (
        find_or_compute h (i, j)
        @@ fun () ->
        try eval grid.(i).(j)
        with Invalid_argument _ -> Erreur (Mauvais_indice (i, j)) )
    | Unaire op ->
        eval_unaire op
    | Binaire op ->
        eval_binaire op
    | Reduction op ->
        eval_reduc op
  in
  fun i j ->
    let r =
      if cycle i j then Erreur Cycle_detecte
      else
        try eval grid.(i).(j)
        with Invalid_argument _ -> Erreur (Mauvais_indice (i, j))
    in
    Hashtbl.replace h (i, j) r ;
    r

let eval_grid (grid : expr array array) : resultat array array =
  let eval = eval grid in
  Array.mapi (fun i -> Array.mapi (fun j _ -> eval i j)) grid
