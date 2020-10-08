(defun mysubst(x y tree)
  (cons (if(consp (car tree))
	    (mysubst x y (car tree))
	  (if(= (car tree) x)
	      y
	    (car tree))) (if(equal nil (cdr tree))
			     nil
			   (mysubst x y (cdr tree)))))
