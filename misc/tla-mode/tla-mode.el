;;
;; tla.el --- Emacs mode for editing TLA+2 files
;;
;; Authors: Damien Doligez <damien.doligez@inria.fr>
;;          Kaustuv Chaudhuri <kaustuv.chaudhuri@gmail.com>
;;
;; Copyright (C) 2009  INRIA and Microsoft Research
;;
;; $Id$

; To use this file, add the following lines to your .emacs
; and uncomment them.

;(load "tla-mode.el")
;(setq tla-enable-abbrevs t)  ; automatic uppercasing of keywords
;(setq tla-hide-on-open t)    ; hide all proof trees on file open
;(setq tla-ellipsis-line t)   ; make ellipsis more visible
;(setq tla-ellipsis-compact t); put ellipsis at the end of the previous line
;(setq tla-ellipsis-string "..."); the string displayed for hidden proofs

(defvar tla-emacs-version-21-or-earlier (< emacs-major-version 22))

;;;;;;;;;;;;;;;; font lock stuff

(make-face 'tla-tabs-face)
(setq tla-tabs-face 'tla-tabs-face)
(set-face-background 'tla-tabs-face "#FF3333")

(make-face 'tla-ellipsis-face)
(setq tla-ellipsis-face 'tla-ellipsis-face)
(set-face-underline-p 'tla-ellipsis-face t)
(set-face-background 'tla-ellipsis-face "#FFFFFE")

(defvar tla-upper-keywords
  '(
    "ASSUME" "ELSE" "LOCAL"
    "ASSUMPTION" "MODULE" "VARIABLE"
    "AXIOM" "EXCEPT" "OTHER" "VARIABLES"
    "CASE" "EXTENDS" "SF_" "WF_"
    "CHOOSE" "IF" "WITH"
    "CONSTANT" "IN" "THEN"
    "CONSTANTS" "INSTANCE" "THEOREM"
    "DOMAIN" "LET"
    "BY" "HAVE" "QED" "TAKE"
    "DEF" "HIDE" "RECURSIVE" "USE"
    "DEFINE" "PROOF" "WITNESS" "PICK"
    "DEFS" "PROVE" "SUFFICES" "NEW"
    "LAMBDA" "STATE" "ACTION" "TEMPORAL"
    "OBVIOUS" "OMITTED" "LEMMA" "COROLLARY" "PROPOSITION" "ONLY"
))

(defvar tla-upper-operators
  '(
    "BOOLEAN" "TRUE" "FALSE" "ENABLED" "UNION" "SUBSET" "UNCHANGED"
))

;; not a keyword, but we still want it auto-upcased
(defvar tla-upper-identifiers '("TLAPS"))

(defvar tla-backslash-upper-keywords
  '(
    "\\A" "\\AA" "\\E" "\\EE"
))

(defvar tla-backslash-upper-operators '("\\X"))

(defvar tla-special-operators
  '("-." "~" "\\lnot" "\\neg" "<>" "=>" "-+->" "<=>" "\\equiv"
    "~>" "#" "/=" "-|" "::=" ":=" "<" "=|" ">" "\\approx"
    "\\asymp" "\\cong" "\\doteq" ">=" "\\geq" "\\gg" "\\notin"
    "<=" "=<" "\\leq" "\\ll" "\\prec" "\\preceq" "\\propto"
    "\\simeq" "\\sqsubset" "\\sqsubseteq" "\\sqsupset"
    "\\sqsupseteq" "\\subset" "\\subseteq" "\\supset" "\\supseteq"
    "|-" "|=" "\\cdot" "@@" ":>" "<:" "\\" "\\cap" "\\in"
    "\\intersect" "\\cup" "\\union" ".." "..." "!!" "##" "$"
    "$$" "??" "\\sqcap" "\\sqcup" "\\uplus" "\\wr" "(+)"
    "\\oplus" "+" "++" "%" "%%" "|" "||" "\\ominus" "--" "-"
    "&" "&&" "(.)" "\\odot" "(/)" "\\oslash" "(\\X)" "\\otimes"
    "*" "**" "/" "//" "\\bigcirc" "\\bullet" "\\div" "\\o"
    "\\circ" "\\star" "^" "^^" "'" "^+" "^*" "^#"

    "\\in" "=" "[]" "@"
))

(defvar tla-backslash-keywords tla-backslash-upper-keywords)

(defvar tla-upper-words
  (append tla-upper-keywords tla-upper-operators tla-upper-identifiers
          tla-backslash-upper-keywords tla-backslash-upper-operators)
)

(defvar tla-operators
  (append tla-upper-operators tla-backslash-upper-operators
          tla-special-operators)
)

(defvar tla-font-lock-keywords
  (let ((max-specpdl-size
         (if tla-emacs-version-21-or-earlier
             (* max-specpdl-size 2)
           max-specpdl-size)))
    (list
     (cons "\\\\\\*.*" 'font-lock-comment-face)
     (list "\\(<\\([0-9]+\\|\\+\\|\\*\\)>[a-zA-Z0-9_]*\\)"
           1 'font-lock-preprocessor-face)
     (regexp-opt tla-upper-keywords 'words)
     (concat (regexp-opt tla-backslash-keywords t) "\\>")
     (cons (regexp-opt tla-operators) 'font-lock-builtin-face)
     (list "\\([a-zA-Z0-9_]+\\).*==" 1 'font-lock-function-name-face)
     (cons "----+" 'font-lock-keyword-face)
     (cons "====+" 'font-lock-keyword-face)
     (cons "\t" 'tla-tabs-face)
)))

; works in emacs 22+
;(defvar tla-syntactic-keywords
;  '(("\\(\\\\\\)\\*.*\\(\n\\)" (1 "<") (2 ">")))
;)

;(defvar tla-syntactic-keywords
;  '(("\\(\\\\\\)\\*.*\\(\n\\)"
;     (1 font-lock-comment-face)
;     (2 font-lock-comment-face)))
;)

(defvar tla-nesting-flag (if tla-emacs-version-21-or-earlier "" "n"))

(defvar tla-syntax-table
  (let ((st (make-syntax-table (standard-syntax-table))))
    (modify-syntax-entry ?\( (concat "()1" tla-nesting-flag) st)
    (modify-syntax-entry ?*  (concat ". 23" tla-nesting-flag) st)
    (modify-syntax-entry ?\) ")(4" st)
    (modify-syntax-entry ?_ "w" st)
    (modify-syntax-entry ?\\ "w" st)
    (modify-syntax-entry ?\" "\"" st)
    st)
  "Syntax table in use in tla-mode."
)

;;;;;;;;;;;;;;;;;;;;;;;;; abbrev stuff

(defun tla-set-abbrevs ()
  (mapcar (lambda (key)
            (define-abbrev local-abbrev-table (downcase key) key () 0 t))
          tla-upper-words))

;;;;;;;;;;;;;;;;;;;;;;;;; outline mode stuff

(defvar tla-outline-regexp
  (concat
   "\\( *\\(<\\([0-9]+\\)>\\|THEOREM\\|LEMMA\\|COROLLARY\\|PROPOSITION\\|----+\\|====+\\)"
      "\\|\\([A-Za-z].*==\\)\\)"))

(defvar tla-leaf-proof-regexp
  "\\((\\*{_}\\*)[ \t\n]*\\)?\\(\\<BY\\>\\|\\<OBVIOUS\\>\\|\\<OMITTED\\>\\)")

(defun tla-outline-level ()
  (save-excursion
    (looking-at tla-outline-regexp)  ;; needed for compatibility with emacs 21
    (let ((num (match-string 3)))
      (if num
          (+ 2 (string-to-number num))
        1)
)))

(defun tla-outline-end-of-heading ()
  (let ((case-fold-search ())
        (leaf-proof (point-max))
        (next-node (point-max)))
    (save-excursion
      (if (re-search-forward tla-leaf-proof-regexp nil 'move)
          (progn
            (goto-char (match-beginning 0))
            (setq leaf-proof (point))
            (re-search-backward "[^ \t]" nil 'move)
            (if (looking-at "\n")
                (progn
                  (re-search-backward "[^ \t\r\n].*$" nil 'move)
                  (goto-char (match-end 0))
                  (forward-char -1)
                  (setq leaf-proof (point)))))))
    (save-excursion
      (forward-line)
      (if (re-search-forward (concat "^" tla-outline-regexp) nil 'move)
          (progn
            (goto-char (match-beginning 1))
            (forward-char -1)
            (setq next-node (point)))))
    (goto-char (min leaf-proof next-node))
))

(defun tla-get-subtree ()
  (let (start end level)
    (save-excursion
      (outline-back-to-heading t)
      (setq start (point))
      (setq level (tla-outline-level))
      (forward-line 1)
      (while (and (or (not (looking-at outline-regexp))
                      (> (tla-outline-level) level))
                  (= (forward-line 1) 0)))
      (setq end (point)))
    (cons start end)
))

(defun tla-get-node ()
  (let (start end)
    (save-excursion
      (outline-back-to-heading t)
      (setq start (point))
      (forward-line 1)
      (while (and (not (looking-at outline-regexp))
                  (= (forward-line 1) 0)))
      (setq end (point)))
    (cons start end)
))

(defun tla-add-ellipsis-lines (local)
  (let* ((subtree (tla-get-subtree))
         (beg (if local (car subtree) (point-min)))
         (end (if local (cdr subtree) (point-max)))
         (ov (overlays-in beg end)))
    (mapcar (lambda (o)
              (cond
               ((equal (overlay-get o 'face) 'tla-ellipsis-face)
                (delete-overlay o))
               ((equal (overlay-get o 'invisible) 'outline)
                (overlay-put (make-overlay (overlay-end o)
                                           (+ 1 (overlay-end o)))
                             'face 'tla-ellipsis-face))))
            ov)
    ())
)

(defun tla-do-nothing (local))

;; this narrows the hidden subproof trees to exactly the
;; hidden text, with some minor heuristics
(defadvice outline-flag-region (before outline-flag-region-check activate)
 "If hiding, change FROM to the first non-whitespace character
following the given FROM, assuming that this character is not
past the given TO.

If unhiding, move the TO to the first non-whitespace character
following the given TO.

Why this magic combination works is left as an exercise to the reader."
 (when (and (equal mode-name "tla") (not tla-ellipsis-compact))
   (if flag
       (save-excursion
         (goto-char from)
         (re-search-forward "^\\s-*" nil 'move)
         (if (<= (point) to)
             (setq from (point))))
     (save-excursion
       (goto-char to)
       (re-search-forward "^\\s-*" nil 'move)
       (setq to (point))))))

(defun tla-beginning-of-visual-line ()
  (beginning-of-line)
  (while (and (get-char-property (point) 'invisible)
              (get-char-property (- (point) 1) 'invisible))
    (forward-char -1)
    (beginning-of-line)
  )
)

; Move the point to some place within the currently displayed header
; above the current point.
(defun tla-move-to-visible-header ()
  (tla-beginning-of-visual-line)
  (if (and (looking-at tla-outline-regexp)
           (equal (get-char-property (match-beginning 2) 'invisible) 'outline))
    (progn (forward-line -1)
           (tla-beginning-of-visual-line))
  )
)

(defun tla-hide-all ()
  (interactive)
  (hide-sublevels 1)
  (tla-update-overlays ())
)

(defun tla-show-all ()
  (interactive)
  (show-all)
  (tla-update-overlays ())
)

(defun tla-hide-node ()
  (interactive)
  (tla-move-to-visible-header)
  (hide-subtree)
  (tla-update-overlays t)
)

(defun tla-show-node ()
  (interactive)
  (tla-move-to-visible-header)
  (show-children)
  (show-entry)
  (tla-update-overlays t)
)

(defun tla-hide-subtree ()
  (interactive)
  (tla-move-to-visible-header)
  (hide-subtree)
  (tla-update-overlays t)
)

(defun tla-show-subtree ()
  (interactive)
  (tla-move-to-visible-header)
  (show-subtree)
  (tla-update-overlays t)
)

(defun tla-show-focus ()
  (interactive)
  (tla-move-to-visible-header)
  (save-excursion
    (hide-sublevels 1)
    (show-entry)
    (show-subtree)
    (outline-back-to-heading t)
    (let ((cur-level (tla-outline-level)))
      (while (> cur-level 1)
        (forward-line -1)
        (outline-back-to-heading t)
        (if (< (tla-outline-level) cur-level)
            (progn
              (setq cur-level (tla-outline-level))
              (show-entry)
              (show-children))))))
  (tla-update-overlays ())
)

;;;;;;;;;;;;;;;;;;;;;;;;; enabling and disabling leaf proofs

(defvar tla-proof-keyword-re
  "\\(BY\\|HAVE\\|OBVIOUS\\|OMITTED\\|TAKE\\|USE\\|WITNESS\\)")

(defun tla-disable-between (start end)
  (save-excursion
    (let ((end-mark (make-marker))
          (case-fold-search ()))
      (set-marker end-mark end)
      (goto-char start)
      (while (re-search-forward
              (concat "\\([ \C-J]\\)" tla-proof-keyword-re "\\>")
              end-mark t)
        (replace-match "\\1(*{_}*)\\2"))
      (set-marker end-mark ())
)))

(defun tla-enable-between (start end)
  (save-excursion
    (let ((end-mark (make-marker))
          (case-fold-search ()))
      (set-marker end-mark end)
      (goto-char start)
      (while (re-search-forward (concat "(\\*{_}\\*)" tla-proof-keyword-re "\\>")
                                end-mark t)
        (replace-match "\\1"))
      (set-marker end-mark ())
)))

(defun tla-disable-all ()
  (interactive)
  (tla-disable-between (point-min) (point-max))
)

(defun tla-enable-all ()
  (interactive)
  (tla-enable-between (point-min) (point-max))
)

(defun tla-disable-subtree ()
  (interactive)
  (let ((range (tla-get-subtree)))
    (tla-disable-between (car range) (cdr range)))
)

(defun tla-enable-subtree ()
  (interactive)
  (let ((range (tla-get-subtree)))
    (tla-enable-between (car range) (cdr range)))
)

(defun tla-disable-node ()
  (interactive)
  (let ((range (tla-get-node)))
    (tla-disable-between (car range) (cdr range)))
)

(defun tla-enable-node ()
  (interactive)
  (let ((range (tla-get-node)))
    (tla-enable-between (car range) (cdr range)))
)

(defun tla-enable-focus ()
  (interactive)
  (tla-disable-all)
  (let ((range (tla-get-subtree)))
    (tla-enable-between (car range) (cdr range)))
)

(defun tla-disable-above (prefix)
 (interactive "p")
 (if (= prefix 4)
     (tla-enable-between (point-min) (point))
   (tla-disable-between (point-min) (point)))
)

;;;;;;;;;;;;;;;;;;;;;;;;; mixing enable and display

(defun tla-focus ()
  (interactive)
  (tla-show-focus)
  (tla-enable-focus)
)

;;;;;;;;;;;;;;;;;;;;;;;;; compilation mode

(defun tla-goto-last-error ()
  (interactive)
  (while (ignore-errors (progn (next-error) t)))
)

;;;;;;;;;;;;;;;;;;;;;;;;; initialization

; override these variables (before calling tla-mode) to customize behaviour

(defvar tla-mode-hook () "Hooks for tla-mode")

(defvar tla-enable-abbrevs ()
  "Set this variable to non-nil before activating tla-mode to get automatic\
   uppercasing of keywords.")

(defvar tla-hide-on-open ()
  "Set this variable to non-nil before activating tla-mode to open files\
   with all proofs hidden.")

(defvar tla-ellipsis-line ()
  "Set this variable to non-nil before activating tla-mode to make ellipsis\
   more visible by displaying a horizontal line from the ellipsis to the\
   right margin.")

(defvar tla-ellipsis-compact ()
  "Set this variable to non-nil to display the ellipsis at the end of the\
   previous header instead of having it on its own line.")

(defvar tla-ellipsis-string "--- proof hidden ---"
  "This string is displayed in place of hidden proofs. It must be set\
   before activating tla-mode to have any effect.")

(defun tla-mode ()
  "Major mode for editing TLA+ code.
\\[tla-mode-map]"
  (interactive)

  (setq major-mode 'tla-mode)
  (setq mode-name "tla")

  (if tla-emacs-version-21-or-earlier
      (put 'tla-mode 'font-lock-defaults
           '(tla-font-lock-keywords () () () ()))
    (setq font-lock-defaults '(tla-font-lock-keywords () () () ()))
  )
;  (set (make-local-variable 'font-lock-syntactic-keywords)
;       tla-syntactic-keywords)
  (set-syntax-table tla-syntax-table)
  (font-lock-mode t)
  (setq indent-tabs-mode nil)

  (if tla-enable-abbrevs
    (progn (tla-set-abbrevs)
           (setq abbrev-mode t)))

  (add-to-invisibility-spec 'tla-mode)

  (if tla-ellipsis-line
      (defalias 'tla-update-overlays 'tla-add-ellipsis-lines)
    (defalias 'tla-update-overlays 'tla-do-nothing))

  (setq buffer-display-table (make-display-table))
  (set-display-table-slot buffer-display-table
                         'selective-display
                         (string-to-vector tla-ellipsis-string))

  (outline-minor-mode 1)
  (set (make-local-variable 'outline-regexp) tla-outline-regexp)
  (set (make-local-variable 'outline-level) 'tla-outline-level)
  (set (make-local-variable 'outline-heading-end-regexp) nil)
  (set (make-local-variable 'comment-start) "(* ")
  (set (make-local-variable 'comment-end) " *)")
  (defalias 'outline-end-of-heading 'tla-outline-end-of-heading)
  (local-set-key (kbd "<C-right>") 'tla-show-node)
  (local-set-key (kbd "<C-kp-right>") 'tla-show-node)
  (local-set-key (kbd "<C-left>") 'tla-hide-node)
  (local-set-key (kbd "<C-kp-left>") 'tla-hide-node)
  (local-set-key (kbd "<C-up>") 'tla-hide-subtree)
  (local-set-key (kbd "<C-kp-up>") 'tla-hide-subtree)
  (local-set-key (kbd "<C-down>") 'tla-show-subtree)
  (local-set-key (kbd "<C-kp-down>") 'tla-show-subtree)
  (local-set-key (kbd "<C-prior>") 'tla-hide-all)
  (local-set-key (kbd "<C-kp-prior>") 'tla-hide-all)
  (local-set-key (kbd "<C-next>") 'tla-show-all)
  (local-set-key (kbd "<C-kp-next>") 'tla-show-all)
  (local-set-key "\C-c\C-a" 'tla-enable-all)
  (local-set-key "\C-c\C-d" 'tla-disable-subtree)
  (local-set-key "\C-c\C-e" 'tla-enable-subtree)
  (local-set-key "\C-c\C-f" 'tla-focus)
  (local-set-key "\C-c\C-l" 'tla-goto-last-error)
  (local-set-key "\C-c\C-n" 'tla-disable-all)
  (local-set-key "\C-c\C-o" 'tla-disable-above)
  (local-set-key "\C-c\C-s" 'tla-show-focus)
  (local-set-key "\C-c\C-t" 'tla-enable-focus)

  (if tla-hide-on-open
      (tla-hide-details))

  (if tla-emacs-version-21-or-earlier
      (run-hooks 'tla-mode-hook)
    (run-mode-hooks 'tla-mode-hook))
)

(add-to-list 'auto-mode-alist '("\\.tla$" . tla-mode))

(provide 'tla-mode)
