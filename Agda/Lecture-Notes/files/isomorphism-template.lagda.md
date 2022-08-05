iso : ? ≅ ?
iso = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : ? → ?
  f = ?

  g : ? → ?
  g = ?

  gf : g ∘ f ∼ id
  gf = ?

  fg : f ∘ g ∼ id
  fg = ?

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
