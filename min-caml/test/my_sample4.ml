let rec f x =
  let rec g y = y + 3
  in
  if g x < 4 then
    3
  else
    (g x) + (f (x-1))
in
f 10
