open Js_of_ocaml

(** node in the DOM tree *)
class type node = Dom.node

(** generic HTML element *)
class type element = Dom_html.element

(**
   All the functions to update and read the DOM tree and update the interface
   more documentation can be found at https://developer.mozilla.org/fr/docs/Web
*)
module Dom : sig
  (** div HTML element *)
  type div = Dom_html.divElement Js.t

  (** text HTML element *)
  type txt = Dom.text Js.t

  (** input HTML element *)
  type input = Dom_html.inputElement Js.t

  (** [appendChild parent child] set the node [child] as direct children of the
     node [parent] in the DOM tree *)
  val appendChild : #node Js.t -> #node Js.t -> unit

  (** HTML element creation module
      The created elements are not in the DOM tree.
      [appenChild] must be called to insert them and see them in the page.
  *)
  module Create : sig
    (** [div ()] returns a new div element. A div is a generic container *)
    val div : unit -> div

    (** [div ()] returns a new input element.
        A basic input where user can type text *)
    val input : unit -> input

    (** [txt s] returns a new text element containing string [s].
        Warning: if [s] is an empty string, the element wont take any space.
        In this case call it with one-space string : [txt " "]
    *)
    val txt : string -> txt
  end

  module Input : sig
    (** [get_value i] returns the value of the input [i] as [string] *)
    val get_value : input -> string

    (** [set_value i s] sets the value of the input [i] to [s] *)
    val set_value : input -> string -> unit
  end

  (** Text elements related module *)
  module Text : sig
    (** [set_content txt s] set [s] as content of a text element *)
    val set_content : txt -> string -> unit
  end

  (** HTML classes related module *)
  module Class : sig
    (** [add e c] adds the class [c] to element [e] *)
    val add : #element Js.t -> string -> unit

    (** [remove e c] removes the class [c] to element [e] *)
    val remove : #element Js.t -> string -> unit
  end

  (** CSS Style related module *)
  module Style : sig
    (** [set_color e c] changes the text color of element [e] to [c] *)
    val set_color : #element Js.t -> string -> unit

    (** [set_background e c] changes the background color
        of element [e] to [c] *)
    val set_background_color : #element Js.t -> string -> unit
  end

  (** JS events related module *)
  module Events : sig
    (** JS events handlers are elements properties in JS that can be
        modified to catch corresponding events. Calling one of those
        function sets the given function as event handler, that will
        be called when the event raises.
    *)

    (** [set_onkeydown i f] sets [f] as handler for the event keydown on
        the input [i], which is raised when a key is pressed on the keyboard.
        [f] takes as parameter the character typed by the user in ASCII
        code and returns a boolean. If [f n] evaluates to [true]
        the inputed character will be actually added to the value, and
        ignored otherwise *)
    val set_onkeydown : input -> (int -> bool) -> unit

    (** [set_onblur i f] sets [f] as handler for the event blur on
        the input [i], which is raised when the focus lefts an element *)
    val set_onblur : input -> (unit -> unit) -> unit

    (** [set_ondblclick e f] sets [f] as handler for the event blur on
        the element [e], which is raised when mouse double-clicks *)
    val set_ondblclick : #element Js.t -> (unit -> unit) -> unit
  end

  module Focus : sig
    (** [focus i] set the focus on the input [i]. On a text edit input, it will
      set the cursor in the text input.
    *)
    val focus : input -> unit

    (** [blur i] removes the focus on the input [i]. BEWARE: calling this
       function will trigger the onblur event
    *)
    val blur : input -> unit
  end

  val get_element_by_id : string -> element Js.t
end

module Init : sig
  (** [set_grid_template e h w] Dynamically set the grid style of the main
      EXCEML element depending on the height and width of the spreadsheet
  *)
  val set_grid_template : #element Js.t -> int -> int -> unit

  (** [build_headers e lines cols] creates headers for lines and columns
      from given list of integers
  *)
  val build_headers : #element Js.t -> int list -> int list -> unit

  (** [onload f] sets the function [f] as the handler for the page loading.
      Can be seen as the page main function *)
  val onload : (unit -> 'a) -> unit
end

module Storage : sig
  (** Remove everything related to ExceML from the localStorage *)
  val clean_all : unit -> unit

  (** [find ()] returns optionnally the localStorage if exist.*)
  val find : unit -> string option

  (** [set s] replaces the local storage by [s] *)
  val set : string -> unit
end
