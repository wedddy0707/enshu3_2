let rec f x =
  if x < 1 then
    0
  else
    f (x - 1)
in
let rec g y =
  if y < 1 then
    0
  else
    (f y) + (g(y - 1))
in
g 10
