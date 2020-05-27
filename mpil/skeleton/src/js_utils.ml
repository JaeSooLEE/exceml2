open Js_of_ocaml

let document = Dom_html.document

let js = Js.string

class type node = Dom.node

class type element = Dom_html.element

module Dom = struct
  include Dom

  type div = Dom_html.divElement Js.t

  type input = Dom_html.inputElement Js.t

  type txt = Dom.text Js.t

  let set_id elt cl = elt##.id := js cl

  module Input = struct
    let get_value elt = elt##.value |> Js.to_string

    let set_value elt s = elt##.value := Js.string s
  end

  module Create = struct
    let div () = Dom_html.createDiv document

    let input () = Dom_html.createInput document

    let txt v = document##createTextNode (js v)
  end

  module Text = struct
    let set_content elt v = elt##.data := Js.string v
  end

  module Class = struct
    let add elt cl = elt##.classList##add (js cl)

    let remove elt cl = elt##.classList##remove (js cl)
  end

  module Style = struct
    let set_color elt color = elt##.style##.color := js color

    let set_background_color elt color =
      elt##.style##.backgroundColor := js color
  end

  module Events = struct
    let handler f = Dom_html.handler (fun t -> f t)

    let set_onkeydown (elt : Dom_html.inputElement Js.t) f =
      elt##.onkeydown :=
        handler (fun t -> if f t##.keyCode then Js._true else Js._false)

    let set_onblur elt f = elt##.onblur := handler (fun _ -> f () ; Js._true)

    let set_ondblclick elt f =
      elt##.ondblclick := handler (fun _ -> f () ; Js._false)
  end

  module Focus = struct
    let focus elt = elt##focus

    let blur elt = elt##blur
  end

  let get_element_by_id = Dom_html.getElementById
end

module Init = struct
  let set_grid_template cells height width =
    let st = Dom_html.createStyle document in
    let css =
      Format.sprintf
        "\n\
         .cells {\n\
        \  grid-template-columns: 40px repeat(%d, calc((100%% - 50px) / %d));\n\
        \    grid-template-rows: repeat(%d, 25px);\n\
         }\n"
        width
        width
        (height + 1)
    in
    st##.innerHTML := js css ;
    Dom.appendChild document##.head st

  let build_headers cells lines columns =
    let mk_header cl v =
      let nd = Dom.Create.div () in
      let t = Dom.Create.txt v in
      Dom.Class.add nd cl ; Dom.appendChild nd t ; Dom.appendChild cells nd
    in
    List.iter (fun i -> mk_header "number" (string_of_int (i + 1))) lines ;
    List.iter (fun j -> mk_header "alphabet" (Tableur.int_to_letter j)) columns

  let onload f =
    Dom_html.window##.onload := Dom_html.handler (fun _ -> f () ; Js._false)
end

module Storage = struct
  open Js

  let storage =
    Optdef.case
      Dom_html.window##.localStorage
      (fun () -> failwith "Storage is not supported by this browser")
      (fun v -> v)

  let key = string "exceml-state"

  let clean_all () = storage##removeItem key

  let find () =
    let r = storage##getItem key in
    Opt.to_option @@ Opt.map r to_string

  let set v = storage##setItem key (string v)

  let init default =
    match find () with None -> set default ; default | Some v -> v
end
