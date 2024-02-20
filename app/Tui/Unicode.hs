module Tui.Unicode
  ( char_update
  , unicode_input_map
  ) where

import Data.List (isPrefixOf, find)

import Data.Text.Zipper (TextZipper, insertChar, insertMany)

char_update :: Char -> [Char] -> (Maybe [Char], TextZipper String -> TextZipper String) 
char_update c cs = case filter (isPrefixOf (cs <> [c]) . fst) unicode_input_map of 
  [] -> case find ((==) cs . fst) unicode_input_map of
    Just (_, out) -> (Nothing, insertMany ([out,c]))
    _ -> (Nothing, (insertMany ((';' : cs) <> [c])))
  [(str, out)]
    | str == cs <> [c] -> (Nothing, insertChar out)
    | otherwise -> (Just (cs <> [c]), id)
  _ -> (Just (cs <> [c]), id)
  

unicode_input_map :: [([Char], Char)]
unicode_input_map =
  [ ("<" , '⟨')
  , (">" , '⟩')
  , ("(" , '⦅')
  , (")" , '⦆')
  , ("(|", '⦇')
  , ("|)", '⦈')
  , ("[" , '⦗')
  , ("]" , '⦘')
  , ("[-", '⹕')
  , ("-]", '⹖')
  , ("[[", '⟦')
  , ("]]", '⟧')
  , ("{" , '⦃')
  , ("}" , '⦄')
  , ("<.", '⦑')
  , (".>", '⦒')
  , ("<<", '《')
  , (">>", '》')
  , ("-<", '⧼')
  , (">-", '⧽')

  -- Combinators/Function Operators
  , ("o", '∘')

  -- Arrows
  , ("to" , '→')
  , ("fm" , '←')
  , ("up" , '↑')
  , ("dn" , '↓')
  , ("To" , '⇒')
  , ("Fm" , '⇐')
  , ("Up" , '⇑')
  , ("Dn" , '⇓')
  , ("mto", '↦')
  , ("mfm", '↤')
  , ("le" , '⮜')
  , ("ri" , '⮞')

  -- Misc. Mathematical Symbols
  , ("O~"  , '⍬')
  , ("O/"  , '∅')
  , ("ex"  , '∃')
  , ("fa"  , '∀')
  , ("in"  , '∈')
  , ("in." , '⋵')
  , ("-."  , '¬')
  , ("/in" , '∉')
  , ("u"   , '∪')
  , ("u|"  , '⊔')
  , ("U"   , '⋃')
  , ("n"   , '∩')
  , ("n|"  , '⊓')
  , ("N"   , '⋂')

  -- numeric & algebraic operations 
  , (":-", '÷')
  , ("x" , '×')
  , ("*" , '⋅')
  , ("v/", '√')
  , ("^" , '∧')
  , ("-^", '⊼')
  , ("v" , '∨')
  , ("-v", '⊽')
  , ("v-", '⊻')
  , ("-.", '¬')
  , ("^^.", '⩑')
  , ("v^.", '⩒')

  -- equality & comparisons
  , ("~=" , '≃')
  , ("~==", '≅')
  , ("^=" , '≜')
  , ("/=" , '≠')
  , ("==" , '≡')
  , ("/==", '≢')
  , ("?=" , '≟')
  , ("o=" , '≗')
  , (">=" , '≥')
  , ("!=" , '≠')
  , ("<=" , '≤')

  -- Sigil specific
  , ("A" , '⍝')
  , ("e|", '⋳')
  , ("|e", '⋻')
  , ("le", '⮜')
  , ("ri", '⮞') 
  , ("de", '≜')
  , ("rc", 'ᛉ')
  , ("rr", 'ᛯ')
  , ("ri", 'ᛣ')
  , ("\\", '﹨')
  , ("...", '…') 
  , ("_[]", '⎕')
  , ("_[]<", '⍃')
  , ("_[]>", '⍄')

  -- shapes/misc. operators
  -- triangles
  , ("|>" , '▷') 
  , ("<|" , '◁') 
  , ("|*>", '▶') 
  , ("<*|", '◀') 
  , ("<*" , '▸') 
  , ("<*" , '◂') 
  -- diamonds & squares
  , ("<>" , '◇') 
  , ("<*>", '◆') 
  , ("[]" , '□') 
  , ("[*]", '■') 

  -- Subscripts
  , ("_0", '₀')
  , ("_1", '₁')
  , ("_2", '₂')
  , ("_3", '₃')
  , ("_4", '₄')
  , ("_5", '₅')
  , ("_6", '₆')
  , ("_7", '₇')
  , ("_8", '₈')
  , ("_9", '₉')
  , ("_=", '₌')
  , ("_-", '₋')
  , ("_+", '₊')
  , ("_a", 'ₐ')
  , ("_e", 'ₑ')
  , ("_h", 'ₕ')
  , ("_i", 'ᵢ')
  , ("_j", 'ⱼ')
  , ("_l", 'ₗ')
  , ("_m", 'ₘ')
  , ("_n", 'ₙ')
  , ("_o", 'ₒ')
  , ("_p", 'ₚ')
  , ("_r", 'ᵣ')
  , ("_s", 'ₛ')
  , ("_t", 'ₜ')
  , ("_u", 'ᵤ')
  , ("_v", 'ᵥ')
  , ("_x", 'ₓ')

  -- greek
  , ("ga", 'α')
  , ("gb", 'β')
  , ("gc", 'ψ')
  , ("gd", 'δ')
  , ("ge", 'ε')
  , ("gf", 'φ')
  , ("gg", 'γ')
  , ("gh", 'η')
  , ("gi", 'ι')
  , ("gj", 'ξ')
  , ("gk", 'κ')
  , ("gl", 'λ')
  , ("gm", 'μ')
  , ("gn", 'ν')
  , ("go", 'ο')
  , ("gp", 'π')
  , ("gr", 'ρ')
  , ("gs", 'σ')
  , ("gt", 'τ')
  , ("gu", 'θ')
  , ("gv", 'ω')
  , ("gw", 'ς')
  , ("gx", 'χ')
  , ("gy", 'υ')
  , ("gz", 'ζ')
  , ("gA", 'Α')
  , ("gB", 'Β')
  , ("gC", 'Ψ')
  , ("gD", 'Δ')
  , ("gE", 'Ε')
  , ("gF", 'Φ')
  , ("gG", 'Γ')
  , ("gH", 'Η')
  , ("gI", 'Ι')
  , ("gJ", 'Ξ')
  , ("gK", 'Κ')
  , ("gL", 'Λ')
  , ("gM", 'Μ')
  , ("gN", 'Ν')
  , ("gO", 'Ο')
  , ("gP", 'Π')
  , ("gR", 'R')
  , ("gS", 'Σ')
  , ("gT", 'Τ')
  , ("gU", 'Θ')
  , ("gV", 'Ω')
  , ("gW", 'Σ')
  , ("gX", 'Χ')
  , ("gY", 'Υ')
  , ("gZ", 'Ζ')

  -- Math double-struck
  , ("sA", '𝔸')
  , ("sB", '𝔹')
  , ("sC", 'ℂ')
  , ("sD", '𝔻')
  , ("sE", '𝔼')
  , ("sF", '𝔽')
  , ("sG", '𝔾')
  , ("sG", 'ℍ')
  , ("sI", '𝕀')
  , ("sJ", '𝕁')
  , ("sK", '𝕂')
  , ("sL", '𝕃')
  , ("sM", '𝕄')
  , ("sN", 'ℕ')
  , ("sO", '𝕆')
  , ("sP", 'ℙ')
  , ("sQ", 'ℚ')
  , ("sR", 'ℝ')
  , ("sS", '𝕊')
  , ("sT", '𝕋')
  , ("sU", '𝕌')
  , ("sV", '𝕍')
  , ("sW", '𝕎')
  , ("sX", '𝕏')
  , ("sY", '𝕐')
  , ("sZ", 'ℤ')

  ]
