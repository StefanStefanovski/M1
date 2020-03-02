(defun mycopy(tree)
  (if(equal nil (cdr tree))
      (cons (car tree) nil)
    (cons (car tree) (mycopy(cdr tree)))))
    
