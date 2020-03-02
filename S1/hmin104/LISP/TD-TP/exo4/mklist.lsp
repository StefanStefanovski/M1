(defun mklist (n)
  (if(= n 0)
      nil
    (cons n (mklist (- n 1)))))
