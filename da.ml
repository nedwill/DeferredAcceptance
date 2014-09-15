open Batteries

type man = M1 | M2 | M3 | M4

type woman = W1 | W2 | W3

type person = M of man | W of woman

(*
let m1list = ref [W W2; W W3; W W1; M M1]
let m2list = ref [W W1; W W3; W W2; M M2]
let m3list = ref [W W3; W W1; W W2; M M3]
let m4list = ref [W W2; W W3; W W1; M M4]
let w1list = ref [M M3; M M1; M M4; W W1; M M2]
let w2list = ref [M M3; M M2; M M1; M M4; W W2]
let w3list = ref [M M2; M M4; M M3; M M1; W W3]
*)

let m1list = ref [W W1; W W2; M M1]
let m2list = ref [W W1; W W2; M M2]
let m3list = ref [W W2; W W1; M M3]
let m4list = ref []
let w1list = ref [M M3; M M1; M M2; W W1]
(*let w2list = ref [M M1; M M3; M M2; W W2]*)
let w2list = ref [M M1; W W2; M M3; M M2]
let w3list = ref []

exception NoChoice

(* person lists *)
let get_top_choice = function
    M M1 -> (match !m1list with [] -> raise NoChoice | p::ps -> let _ = m1list := ps in p)
  | M M2 -> (match !m2list with [] -> raise NoChoice | p::ps -> let _ = m2list := ps in p)
  | M M3 -> (match !m3list with [] -> raise NoChoice | p::ps -> let _ = m3list := ps in p)
  | M M4 -> (match !m4list with [] -> raise NoChoice | p::ps -> let _ = m4list := ps in p)
  | W W1 -> (match !w1list with [] -> raise NoChoice | p::ps -> let _ = w1list := ps in p)
  | W W2 -> (match !w2list with [] -> raise NoChoice | p::ps -> let _ = w2list := ps in p)
  | W W3 -> (match !w3list with [] -> raise NoChoice | p::ps -> let _ = w3list := ps in p)

exception NoRank

let get_rank ask =
  let r l = match List.index_of ask l with None -> raise NoRank | Some x -> x in
  function
    M M1 -> r !m1list
  | M M2 -> r !m2list
  | M M3 -> r !m3list
  | M M4 -> r !m4list
  | W W1 -> r !w1list
  | W W2 -> r !w2list
  | W W3 -> r !w3list

let get_pref_list = function
    M M1 -> !m1list
  | M M2 -> !m2list
  | M M3 -> !m3list
  | M M4 -> !m4list
  | W W1 -> !w1list
  | W W2 -> !w2list
  | W W3 -> !w3list

type proposal = man * woman

exception Empty

let print s = Printf.printf "%s" s

(* men: if man not in match list, make next offer *)
(* women: if more than one man offer, drop the highest one (print that this happened) *)
(* done: number of matches after this is equal to number of men *)

let in_pair p =
  (match p with
    M m -> (function
      M m1, M m2 -> m1 = m || m2 = m
    | M m1, W _ -> m1 = m
    | W _, M m2 -> m2 = m
    | W _, W _ -> false)
  | W w -> (function
     M _, M _ -> false
    | M _, W w2 -> w2 = w
    | W w1, M _ -> w1 = w
    | W w1, W w2 -> w1 = w || w2 = w))

let ex l (p : person) = List.exists (in_pair p) (l : (person * person) list)

let current_matches = ref []

let per_to_string = function
    M M1 -> "M1"
  | M M2 -> "M2"
  | M M3 -> "M3"
  | M M4 -> "M4"
  | W W1 -> "W1"
  | W W2 -> "W2"
  | W W3 -> "W3"

let pair_to_string (p1, p2) = "(" ^ per_to_string p1 ^ ", " ^ per_to_string p2 ^ ")"

let print_prop (p1,p2) =
  let (s1,s2) = (per_to_string p1, per_to_string p2) in
  Printf.printf "%s proposes to %s.\n" s1 s2

let rec pairs_to_string = function
    [] -> "no pairs"
  | [pr] -> pair_to_string pr
  | pr::prs -> pairs_to_string prs ^ ", " ^ pair_to_string pr 

let print_matches () =
  let s = pairs_to_string !current_matches in
  Printf.printf "matches: %s\n" s

let rec pers_to_string = function
    [] -> "no people"
  | [pr] -> per_to_string pr
  | pr::prs -> per_to_string pr ^ "; " ^ pers_to_string prs

let print_rejects rejects = Printf.printf "Rejects: %s\n" (pers_to_string rejects)

let maybe_make_proposal p =
  let starting_matches = !current_matches in
  if not (ex starting_matches p)
  then
    let partner = get_top_choice p in
    let prop = (p, partner) in
    let _ = print_prop prop in
    (*
    let _ = print "Before adding..." in
    let _ = print_matches () in
  *)
    let _ = current_matches := prop::starting_matches in
    (*
    let _ = print "After adding..." in
    let _ = print_matches () in
  *)
    ()
  else ()

exception NotInPair

let unwrap_pair p = function (p1,p2) -> if p1 = p then p2 else p1

let all_matches l p = List.map (unwrap_pair p) (List.filter (in_pair p) l)

let rank_info p ask = (ask, get_rank ask p)

let prefer_self p ask =
  let pref_list = get_pref_list p in
  let self_rank = List.index_of p pref_list in
  let ask_rank = List.index_of ask pref_list in
  self_rank < ask_rank

let best_suitor sl =
  let ranks_only = List.map (fun (_,r) -> r) sl in
  let min_rank = List.min ranks_only in
  List.find (fun (_,r) -> r = min_rank) sl

let print_reject_msg p ask =
  let _ = Printf.printf "%s gets rejected by %s.\n" (per_to_string ask) (per_to_string p) in
  ()

let rem_pair_matches ask =
  let check pr = not (in_pair ask pr) in
  let _ = current_matches := List.filter check !current_matches in
  ()

let reject p ask =
  let _ = print_reject_msg p ask in
  let _ = rem_pair_matches ask in
  ()

let maybe_make_rejection p =
  match all_matches !current_matches p with
    [] -> ()
  | [ask] -> if prefer_self p ask then reject p ask else ()
  | l ->
    let with_rank_info = List.map (rank_info p) l in
    let best = best_suitor with_rank_info in
    let (best_name, best_rank) = best in
    let rejects = List.filter (fun s -> s <> best) with_rank_info in
    let reject_names = List.map (fun (n,_) -> n) rejects in
    let _ = List.iter (reject p) reject_names in
    let _ = if prefer_self p best_name then reject p best_name else () in
    ()

let da suitors suitees =
  let rec helper () =
  (*
    let _ = print "Before proposals..." in
    let _ = print_matches () in
  *)
    let _ = List.iter maybe_make_proposal suitors in
    (*
    let _ = print "Before rejections..." in
    let _ = print_matches () in
  *)
    let _ = List.iter maybe_make_rejection suitees in
    let _ = print "After this round of propsals and rejections, we have " in
    let _ = print_matches () in
    let finished = List.length !current_matches = List.length suitors in
    if finished then () else (helper ())
  in (helper ())

(*
let man_proposing_da () =
  let suitors = [M M1; M M2; M M3; M M4] in
  let suitees = [W W1; W W2; W W3] in
  da suitors suitees

let woman_proposing_da () =
  let suitors = [W W1; W W2; W W3] in
  let suitees = [M M1; M M2; M M3; M M4] in
  da suitors suitees
*)

let man_proposing_da () =
  let suitors = [M M1; M M2; M M3] in
  let suitees = [W W1; W W2] in
  da suitors suitees

(* let _ = man_proposing_da () *)

let _ = man_proposing_da ()
