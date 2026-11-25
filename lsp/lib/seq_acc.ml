type 'a t = { mutable seq : 'a Seq.t; mutable acc : 'a list }

let make seq = { seq; acc = [] }

let take t =
  let x, seq = Seq.uncons t.seq |> Option.get in
  t.seq <- seq;
  t.acc <- x :: t.acc;
  x

let acc t = List.rev t.acc
