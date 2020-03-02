(defun rmv(x l)
  (if l
      (if(= x (car l))
	  (rmv x (cdr l))
	(cons (car l) (rmv x (cdr l))))
    l))
