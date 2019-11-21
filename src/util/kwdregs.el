(defun doit (l)
  (let ((res (prin1-to-string (regexp-opt l))))
    (setq res (replace-regexp-in-string "\\?:" "" res))
    (setq res (replace-regexp-in-string "^\"" "\"^\\\\\\\\(" res))
    (setq res (replace-regexp-in-string "\"$" "\\\\\\\\)$\"" res))
    res))

(let ((i
       (format
        ";;; (Str.regexp %s, Str.regexp %s, Str.regexp %s, Str.regexp %s)"
        (doit '( "ASSUME" "ASSUMPTION" "AXIOM" "BOOLEAN" "CASE" "CHOOSE" "CONSTANT" "CONSTANTS"
                 "BY" "DEF" "DEFINE" "DEFS" "LAMBDA" "OBVIOUS" "ELSE"
                 "EXCEPT" "EXTENDS" "IF" "IN" "INSTANCE" "LET" "HAVE" "TRUE" "FALSE"
                 "HIDE" "PROOF" "PROVE" "STATE" "OMITTED" "LOCAL" "MODULE" "OTHER" "SF_"
                 "THEN" "THEOREM" "COROLLARY" "UNCHANGED" "QED" "RECURSIVE" "WITNESS" "SUFFICES"
                 "ACTION" "LEMMA" "VARIABLE" "VARIABLES" "WF_" "WITH" "TAKE"
                 "USE" "PICK" "NEW" "TEMPORAL" "PROPOSITION" "ONLY"))
        (doit '( "-." "~" "\\lnot" "\\neg" "[]" "<>" "DOMAIN" "ENABLED" "SUBSET" "UNCHANGED" "UNION"))
        (doit '( "=>" "-+->" "<=>" "\\equiv" "~>" "#" "/=" "-|" "::=" ":=" "<" "=" "=|"
                 ">" "\\approx" "\\asymp" "\\cong" "\\doteq" ">=" "\\geq" "\\gg"
                 "\\notin" "<=" "=<" "\\leq" "\\ll" "\\prec" "\\preceq" "\\propto"
                 "\\simeq" "\\sqsubset" "\\sqsubseteq" "\\sqsupset"
                 "\\sqsupseteq" "\\subset" "\\subseteq" "\\supset" "\\supseteq"
                 "|-" "|=" "\\cdot" "@@" ":>" "<:" "\\" "\\cap" "\\in" "\\intersect" "\\cup"
                 "\\union" ".." "..." "!!" "##" "$" "$$" "??" "\\sqcap" "\\sqcup"
                 "\\uplus" "\\wr" "(+)" "\\oplus" "+" "++" "%" "%%" "|" "||" "\\ominus" "--" "-"
                 "&" "&&" "(.)" "\\odot" "(/)" "\\oslash" "(\\X)" "\\X" "\\times" "\\otimes" "*" "**" "/" "//"
                 "\\bigcirc" "\\bullet" "\\div" "\\o" "\\circ" "\\star" "^" "^^" ))
        (doit '( "'" "^+" "^*" "^#" )))))
  (end-of-buffer)
  (insert i))


;;; Run the following steps in order
;;;
;;; 1. bring the cursor below to the X between the [ and ]
;;;
;;; 2. run M-x eval-buffer
;;;
;;; [ ]
