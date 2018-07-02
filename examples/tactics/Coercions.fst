module Coercions

open FStar.Tactics


let tm : term = Tv_App (Tv_App (`op_Addition) (`1, Q_Explicit)) (`2, Q_Explicit)

let basic : int =
  match tm with
  | Tv_App l _ -> 1
  | _ -> 2

let one : option term =
  match tm with
  | Tv_App l _ -> begin match l with
                  | Tv_App _ (x, _) -> Some x
                  | _ -> None
                  end
  | _ -> None

let two : option term =
  match tm with
  | Tv_App _ (x, _) -> Some x
  | _ -> None

let _ = assert_by_tactic True
        (fun () -> print ("tm = "  ^ term_to_string tm);
                   print ("one = " ^ (match one with | Some x -> term_to_string x | None -> "NONE?"));
                   print ("two = " ^ (match two with | Some x -> term_to_string x | None -> "NONE?"));
                   ())

(* Nested patterns! *)
let test tm : option term =
  match tm with
  | Tv_App (Tv_App _ (x, _)) _ -> Some x
  | _ -> None
