let state = ref false
let lock = Mutex.create ()
let is_interrupted () = Mutex.protect lock (fun () -> !state)

let mark_interrupted () =
  Mutex.protect lock (fun () ->
      let was = !state in
      state := true;
      was)
