(defvar haskenthetical-mode-syntax-table
  "Syntax table for `haskenthetical-mode'.")

(setq haskenthetical-mode-syntax-table
      (let ((tab (make-syntax-table)))
        ; These set "#" followed by whitespace to start a comment, and newline
        ; to end it. "#!" followed by whitespace should also be a comment, but
        ; syntax tables don't support that.
        (modify-syntax-entry ?# ". 1" tab)
        (modify-syntax-entry ?  "- 2" tab)
        (modify-syntax-entry ?\t "- 2" tab)
        (modify-syntax-entry ?\n "> - 2" tab)
        tab))

(define-derived-mode haskenthetical-mode prog-mode "hth"
  (setq font-lock-defaults '(nil))
  (setq-local comment-start "#"))

(provide 'haskenthetical-mode)
