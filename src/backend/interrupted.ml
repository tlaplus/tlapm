let state = ref false
let lock = Mutex.create ()

let is_interrupted () =
  Mutex.lock lock;
  let state_val = !state in
  Mutex.unlock lock;
  state_val

let mark_interrupted () =
  Mutex.lock lock;
  let old_state = !state in
  state := true;
  Mutex.unlock lock;
  old_state
