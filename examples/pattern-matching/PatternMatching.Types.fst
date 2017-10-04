module PatternMatching.Types

open FStar.Tactics

type var = binder
type qn = list string

type pattern =
| SPAny: pattern
| SPVar: var: var -> pattern
| SPQn: qn: qn -> pattern
| SPApp: hd: pattern -> arg: pattern -> pattern
