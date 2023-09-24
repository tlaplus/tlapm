type mode = Initializing | Ready | Shutdown
type t = { mode : mode; docs : Tlapm_lsp_docs.t }

let empty = { mode = Initializing; docs = Tlapm_lsp_docs.empty }

let ready st =
  match st.mode with
  | Initializing -> { st with mode = Ready }
  | Ready -> st
  | Shutdown -> st

let shutdown st =
  match st.mode with
  | Initializing -> { st with mode = Shutdown }
  | Ready -> { st with mode = Shutdown }
  | Shutdown -> st

let handle_if_ready st f =
  match st.mode with
  | Initializing -> Error "initializing"
  | Ready -> Ok { st with docs = f st.docs }
  | Shutdown -> Error "going to shutdown"

let handle_if_ready_silent st f =
  match handle_if_ready st f with
  | Ok st' -> st'
  | Error err ->
      Eio.traceln "Ignoring request: %s" err;
      st
