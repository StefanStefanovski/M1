(defun factn(n)
  (if (= n 0)
      1
    (* n (factn(- n 1)))))
 
