{
open Lexing
open Parser
}

let space = ' ' | '\t' | '\r'

rule token = parse
  | "not"    { NOT }
  | "¬"      { NOT }
  | "fun"    { FUN }
  | "λ"      { FUN }
  | "󰘧"      { FUN }
  | "fst"    { FST }
  | "π₁"     { FST }
  | "𝛑₁"     { FST }
  | "snd"    { SND }
  | "π₂"     { SND }
  | "𝛑₂"     { SND }
  | "case"   { CASE }
  | "of"     { OF }
  | "left"   { LEFT }
  | "right"  { RIGHT }
  | "absurd" { ABSURD }
  | "T"      { TRUE }
  | "⊤"      { TRUE }
  | "_"      { FALSE }
  | "⊥"      { FALSE }
  | "|"      { BAR }
  | "=>"     { IMP }
  | "⇒"      { IMP }
  | "/\\"    { AND }
  | "∧"      { AND }
  | "\\/"    { OR }
  | "∨"      { OR }
  | "("      { LPAR }
  | ")"      { RPAR }
  | ":"      { COLON }
  | ","      { COMMA }
  | "->"     { TO }
  | "→"      { TO }
  | "Nat"    { NAT }
  | "ℕ"      { NAT }
  | "Rec"    { REC }
  | "rec"    { REC }
  | "Zero"   { ZERO }
  | "Succ"   { SUCC }
  | "succ"   { SUCC }
  | (['A'-'Z''a'-'z''0'-'9']+ as s) { IDENT s }
  | space+ { token lexbuf }
  | "\n" { new_line lexbuf; token lexbuf }
  | eof { EOF }
