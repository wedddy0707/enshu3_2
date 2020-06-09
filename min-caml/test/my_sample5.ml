let rec even n =
  let rec odd n =
    if n = 1 then
      1
    else
      even (n-1)
  in
  if n = 0 then
    1
  else
    odd (n-1)
in
even 6

