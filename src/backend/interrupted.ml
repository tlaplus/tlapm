let state = Atomic.make false
let is_interrupted () = Atomic.get state
let mark_interrupted () = Atomic.exchange state true
