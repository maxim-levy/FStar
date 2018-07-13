module PatAnnot
open FStar.List.Tot

let f () = (), ()

[@expect_failure]
let whoops : squash False =
  match f () with
  | _, (x : squash False) -> x

[@expect_failure]
let whoops2 : squash False =
  let _, (x:unit{False}) = f () in
  assert False

[@expect_failure]
let sub_bv : squash False =
  let _, (l:list int{False}) = splitAt 0 [1;2;3] in
  assert False

[@expect_failure]
let s : squash False =
    match () with
    | (x : squash False) -> x
