open Js_utils
open Parser

let range i j = List.init (j - i + 1) (fun x -> x + i)

type cell_infos = {
  container : Dom.div;
  inp : Dom.input;
  txt : Dom.txt;
  mutable result : Tableur.resultat;
  mutable parent_deps : Tableur.CaseSet.elt list;
  mutable child_deps : Tableur.CaseSet.elt list;
}

exception Bad_Storage_format of string

let direct_deps expr =
  let rec aux expr =
    let open Tableur in
    match expr with
    | Vide | Entier _ | Flottant _ | Chaine _ ->
        CaseSet.empty
    | Case (i, j) ->
        CaseSet.singleton (i, j)
    | Unaire {operande; _} ->
        aux operande
    | Binaire {gauche; droite; _} ->
        CaseSet.union (aux gauche) (aux droite)
    | Reduction {case_debut; case_fin; _} ->
        List.fold_left (fun set c -> CaseSet.add c set) CaseSet.empty
        @@ coords_of_plage case_debut case_fin
  in
  Tableur.CaseSet.elements (aux expr)

type grid = Tableur.expr array array

type infos_grid = cell_infos array array

let mk_cell ?(inp = Dom.Create.input ()) ?(container = Dom.Create.div ())
    ?(txt = Dom.Create.txt " ") ?(result = Tableur.RVide) ?(parent_deps = []) ?(child_deps = [])() =
  {inp; container; txt; result; parent_deps; child_deps}

let error_to_string e =
  match e with
  |Tableur.Mauvais_indice _ -> Printf.sprintf "!IndexError!"
  |Tableur.Argument_BinOp_invalide |Tableur.Argument_invalide -> Printf.sprintf "!!ArgErrors!!"
  |Tableur.Cycle_detecte -> Printf.sprintf "!!Cycle!!"

let resultat_to_string r =
  let pretty_string s=
    let st = String.sub s 0 7 in
    let dots = Printf.sprintf "%c%c%c" '.' '.' '.' in
    let sl = dots::[] in
    String.concat "" (st::sl)
  in
  match r with
  |Tableur.RVide | Tableur.RInitial -> ""
  |Tableur.RChaine (s) -> if String.length s > 7 then
      pretty_string s
    else
      s
  |Tableur.REntier (n) -> Printf.sprintf "%*g" 5 (float_of_int n)
  |Tableur.RFlottant (f) -> Printf.sprintf "%*g" 5 f
  |Tableur.Erreur e -> error_to_string e

let update_display infos_grid i j r =
  let integ_cell_err r =
    match r with
    |Tableur.Erreur e ->  Dom.Class.add infos_grid.(i).(j).container "cell-error"
    |_ -> Dom.Class.remove infos_grid.(i).(j).container "cell-error"
  in
  let s = resultat_to_string r in
  integ_cell_err r;
  Dom.Text.set_content infos_grid.(i).(j).txt s

let update_deps infos_grid i j expr =
let cell = infos_grid.(i).(j) in
let exp v = match Ast.make v with
  |Ok(e) -> e
  |_-> Tableur.Chaine("Syntax error")
in
let e = exp expr in
cell.parent_deps <- (direct_deps e);
let add_child p =
  let (a, b) = p in
  let setP = Tableur.CaseSet.of_list infos_grid.(a).(b).child_deps in
  let setN = Tableur.CaseSet.union (Tableur.CaseSet.singleton (i, j)) setP in
  infos_grid.(a).(b).child_deps <- Tableur.CaseSet.elements setN
in
List.iter add_child cell.parent_deps;
e

let rec propagate grid infos_grid i j =
  let update_child p =
    let (a,b) = p in
    let cell = infos_grid.(a).(b) in
    let r = Tableur.eval_expr grid grid.(a).(b) in
    cell.result <- (r);
    update_display infos_grid a b r;
    match r with
    |Tableur.Erreur e -> ()
    |_ -> propagate grid infos_grid a b

  in
  List.iter update_child infos_grid.(i).(j).child_deps


let grid_to_string grid infos_grid =  (*assert false TODO *)
  let cell_to_string i j grid infos_grid =
    let cell = grid.(i).(j) in
    match cell with
    |Tableur.Vide -> None
    |_ -> Some(Printf.sprintf "%d|%d|%s"  i j (Dom.Input.get_value infos_grid.(i).(j).inp))
  in
  let grid_string = Array.mapi (fun i a -> Array.mapi (fun j c -> cell_to_string i j grid infos_grid) a) grid in
  let acc l a =
    match a with
    |Some(x) -> x::l
    |_-> l
  in
  let s = Array.fold_left List.append [] (Array.map (fun a -> Array.fold_left acc [] a) grid_string) in
  String.concat "~" s



let cells_of_string storage_grid = (* assert false TODO *)
  let ls = String.split_on_char '~' storage_grid in
  let read_cell strg =
    let l = String.split_on_char '|' strg in
    match l with
    |is::js::l ->let i = int_of_string is in
        let j = int_of_string js in
        let lmatcher lparam =
          match lparam with
          |a::[] -> a
          |a::n -> String.concat "|" l
          |_ -> raise(Bad_Storage_format "Mauvais format de sauvegarde")
      in
      let l2 = lmatcher l in
        (i, j, l2)
    |_ -> raise(Bad_Storage_format "Mauvais format de sauvegarde")
  in
  try
    List.map read_cell ls
  with
  | _ -> []




let update i j grid infos_grid =
  let cell = infos_grid.(i).(j) in
  let e = update_deps infos_grid i j (Dom.Input.get_value cell.inp) in
  let r = Tableur.eval_expr grid e in
  grid.(i).(j)<-(e);
  cell.result <- (r);
  Dom.Class.remove cell.inp "editing-input";
  Storage.set (grid_to_string grid infos_grid);
  update_display infos_grid i j r;
  propagate grid infos_grid i j




let add_cell_events i j grid infos_grid =  (* assert false TODO *)
  let cell = infos_grid.(i).(j) in
  let fdblclick () =
    Dom.Class.add cell.inp "editing-input";
    Dom.Focus.focus cell.inp
  in
  let fonblur () =
    update i j grid infos_grid
  in
  let fonkeydown n =
    if n = 13 then begin
      Dom.Focus.blur cell.inp;
      false
    end
    else
      true
  in
  Dom.Events.set_ondblclick cell.container fdblclick;
  Dom.Events.set_onblur cell.inp fonblur;
  Dom.Events.set_onkeydown cell.inp fonkeydown



let build_cell cells =  (* TODO Question 1 *)
  let cell = mk_cell () in
  Dom.appendChild cell.container cell.inp;
  Dom.appendChild cell.container cell.txt;
  Dom.Class.add cell.container "cell-container";
  Dom.appendChild cells cell.container;
  cell

let load_grids height width =
  let cells = Dom.get_element_by_id "cells" in
  Init.set_grid_template cells height width ;
  let lines = range 0 (height - 1) in
  let columns = range 0 (width - 1) in
  Init.build_headers cells lines columns ;
  let grid = Array.make_matrix height width Tableur.Vide in
  let infos_grid =
    Array.init height @@ fun _ -> Array.init width @@ fun _ -> build_cell cells
  in
  (grid, infos_grid)

let load_storage grid infos_grid =
  let strgef ()= match Storage.find () with
    |Some(s) -> s
    |None -> ""
  in
  let strge = strgef () in
  let push_cell sr =
    let (i, j, s) = sr in
    let tmp = update_deps infos_grid i j s in
    Dom.Input.set_value infos_grid.(i).(j).inp s;
    update i j grid infos_grid
  in
  let ls = cells_of_string strge in
  List.iter push_cell ls


let main () =
  let height = 10 in
  let width = 10 in
  let (grid, infos_grid) = load_grids height width in
  let () = load_storage grid infos_grid in
  Array.iteri
    (fun i a -> Array.iteri (fun j c -> add_cell_events i j grid infos_grid) a)
    grid

let () = Init.onload main
